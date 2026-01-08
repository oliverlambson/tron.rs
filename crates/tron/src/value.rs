#[derive(Debug, PartialEq)]
pub enum ValueType<'a> {
    Nil,
    Bit(bool),
    I64(i64),
    F64(f64),
    Txt(&'a str),
    Bin(&'a [u8]),
    Arr(u32),
    Map(u32),
}

impl<'a> ValueType<'a> {
    pub fn new(data: &'a [u8]) -> Option<Self> {
        let first_byte = data.first()?;
        match first_byte & 0b00000111 {
            // nil
            0 => {
                // high bits must be 0
                (first_byte & 0b11111000 == 0).then_some(ValueType::Nil)
            }
            // bit
            1 => {
                // high bits excl. last must be 0
                (first_byte & 0b11110000 == 0)
                    .then_some(ValueType::Bit(first_byte & 0b00001000 == 0b00001000))
            }
            // i64
            2 => Some(ValueType::I64(i64::from_le_bytes(
                data.get(1..9)?.try_into().ok()?,
            ))),
            // f64
            3 => Some(ValueType::F64(f64::from_le_bytes(
                data.get(1..9)?.try_into().ok()?,
            ))),
            // txt - utf8 encoded string
            4 => {
                let (l, offset) = Self::decode_length(data)?;
                Some(ValueType::Txt(
                    std::str::from_utf8(data.get(offset..offset + l)?).ok()?,
                ))
            }
            // bin - raw bytes
            5 => {
                let (l, offset) = Self::decode_length(data)?;
                Some(ValueType::Bin(data.get(offset..offset + l)?))
            }
            // arr - root node offset (1-4 bytes, little-endian)
            6 => {
                let m = ((first_byte >> 3) & 0b11) as usize;
                let l = m + 1;
                let bytes = data.get(1..1 + l)?;
                let mut buf = [0u8; 4];
                buf[..l].copy_from_slice(bytes);
                Some(ValueType::Arr(u32::from_le_bytes(buf)))
            }
            // map - root node offset (1-4 bytes, little-endian)
            7 => {
                let m = ((first_byte >> 3) & 0b11) as usize;
                let l = m + 1;
                let bytes = data.get(1..1 + l)?;
                let mut buf = [0u8; 4];
                buf[..l].copy_from_slice(bytes);
                Some(ValueType::Map(u32::from_le_bytes(buf)))
            }
            _ => unreachable!(),
        }
    }

    /// Returns (length, offset) for variable-length types
    fn decode_length(data: &[u8]) -> Option<(usize, usize)> {
        let first_byte = data.first()?;
        let l = (first_byte >> 4) as usize;
        let is_packed = first_byte & 0b00001000 == 0b00001000;
        if is_packed {
            Some((l, 1))
        } else {
            let n = l;
            let bytes = data.get(1..1 + n)?;
            let mut buf = [0u8; 8];
            buf[..n].copy_from_slice(bytes);
            let length = usize::from_le_bytes(buf);
            Some((length, 1 + n))
        }
    }

    /// Returns total byte length of value record (tag + payload)
    pub fn byte_len(data: &[u8]) -> Option<usize> {
        match data.first()? & 0b111 {
            0 | 1 => Some(1), // nil, bit: just tag
            2 | 3 => Some(9), // i64, f64: tag + 8 bytes
            4 | 5 => {
                // txt, bin
                let (length, offset) = Self::decode_length(data)?;
                Some(offset + length) // tag + (offset - 1) + length
            }
            6 | 7 => {
                //  arr, map
                let m = ((data.first()? >> 3) & 0b11) as usize;
                let l = 1 + m;
                Some(1 + l) // tag + L bytes
            }
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_nil() {
        let data = [0x00];
        assert_eq!(ValueType::new(&data), Some(ValueType::Nil));
        assert_eq!(ValueType::byte_len(&data), Some(1));
    }

    #[test]
    fn parse_bit_false() {
        let data = [0x01];
        assert_eq!(ValueType::new(&data), Some(ValueType::Bit(false)));
        assert_eq!(ValueType::byte_len(&data), Some(1));
    }

    #[test]
    fn parse_bit_true() {
        let data = [0x09];
        assert_eq!(ValueType::new(&data), Some(ValueType::Bit(true)));
        assert_eq!(ValueType::byte_len(&data), Some(1));
    }

    #[test]
    fn parse_i64() {
        let data = [0x02, 0xD2, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        assert_eq!(ValueType::new(&data), Some(ValueType::I64(1234)));
        assert_eq!(ValueType::byte_len(&data), Some(9));
    }

    #[test]
    fn parse_f64() {
        let data = [0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xF8, 0x3F];
        assert_eq!(ValueType::new(&data), Some(ValueType::F64(1.5)));
        assert_eq!(ValueType::byte_len(&data), Some(9));
    }

    #[test]
    fn parse_txt_packed() {
        let data = [0x2C, 0x68, 0x69]; // "hi"
        assert_eq!(ValueType::new(&data), Some(ValueType::Txt("hi")));
        assert_eq!(ValueType::byte_len(&data), Some(3));
    }

    #[test]
    fn parse_txt_unpacked() {
        // "0123456789abcdef" (16 chars, can't fit in packed 0-15)
        let data = [
            0x14, // tag: txt (100), unpacked (0), N=1 byte for length
            0x10, // length: 16
            // payload
            0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, // "0123456789"
            0x61, 0x62, 0x63, 0x64, 0x65, 0x66, // "abcdef"
        ];
        assert_eq!(
            ValueType::new(&data),
            Some(ValueType::Txt("0123456789abcdef"))
        );
        assert_eq!(ValueType::byte_len(&data), Some(18)); // 1 tag + 1 len + 16 payload
    }

    #[test]
    fn parse_bin_packed() {
        let data = [0x3D, 0xAA, 0xBB, 0xCC];
        assert_eq!(
            ValueType::new(&data),
            Some(ValueType::Bin(&[0xAA, 0xBB, 0xCC]))
        );
        assert_eq!(ValueType::byte_len(&data), Some(4));
    }

    #[test]
    fn parse_bin_unpacked() {
        // 16 bytes (can't fit in packed 0-15)
        let data = [
            0x15, // tag: bin (101), unpacked (0), N=1 byte for length
            0x10, // length: 16
            // payload
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D,
            0x0E, 0x0F,
        ];
        assert_eq!(
            ValueType::new(&data),
            Some(ValueType::Bin(&[
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D,
                0x0E, 0x0F,
            ]))
        );
        assert_eq!(ValueType::byte_len(&data), Some(18)); // 1 tag + 1 len + 16 payload
    }

    #[test]
    fn parse_arr() {
        let data = [0x06, 0x10]; // offset 0x10
        assert_eq!(ValueType::new(&data), Some(ValueType::Arr(0x10)));
        assert_eq!(ValueType::byte_len(&data), Some(2));
    }

    #[test]
    fn parse_map() {
        let data = [0x07, 0x20]; // offset 0x20
        assert_eq!(ValueType::new(&data), Some(ValueType::Map(0x20)));
        assert_eq!(ValueType::byte_len(&data), Some(2));
    }
}
