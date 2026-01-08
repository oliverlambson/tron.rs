//! Scalar document.

use std::borrow::Cow;

use crate::document::SCALAR_MAGIC;
use crate::value::ValueType;

/// Parsed scalar document containing a single value.
#[derive(Debug, PartialEq)]
pub struct ScalarDocument<'a> {
    data: Cow<'a, [u8]>,
    pub value: ValueType<'a>,
}
impl<'a> ScalarDocument<'a> {
    /// Parse a scalar document from raw bytes.
    /// Returns None if:
    /// - Document is too short (< 5 bytes)
    /// - Missing NORT terminator
    /// - Value doesn't end exactly at terminator
    pub fn new(data: &'a [u8]) -> Option<Self> {
        // minimum length 5 bytes (1 tag + 4 NORT)
        if data.len() < 5 {
            return None;
        }

        // last 4 bytes == NORT
        if data.get(data.len() - 4..)? != SCALAR_MAGIC {
            return None;
        }

        // parse value
        let value_data = &data[..data.len() - 4];
        let value = ValueType::new(value_data)?;

        // verify value ends exactly at NORT boundary (is this necessary?)
        let value_len = ValueType::byte_len(value_data)?;
        if value_len != value_data.len() {
            return None;
        }

        Some(Self {
            data: Cow::Borrowed(data),
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_output_from_tron_go() {
        //! generated these byte arrays from tron-go

        // Value{Type: tron.TypeNil}
        // encoded value:    0x00
        // encoded document: 0x00, 0x4e, 0x4f, 0x52, 0x54
        //                 | tag | NORT trailer --------- |
        let data: [u8; _] = [0x00, 0x4e, 0x4f, 0x52, 0x54];
        let doc = ScalarDocument::new(&data).unwrap();
        assert_eq!(doc.value, ValueType::Nil);

        // Value{Type: tron.TypeBit, Bool: true}
        // encoded value:    0x09
        // encoded document: 0x09, 0x4e, 0x4f, 0x52, 0x54
        //                 | tag | NORT trailer --------- |
        let data: [u8; _] = [0x09, 0x4e, 0x4f, 0x52, 0x54];
        let doc = ScalarDocument::new(&data).unwrap();
        assert_eq!(doc.value, ValueType::Bit(true));

        // Value{Type: tron.TypeI64, I64: 1234}
        // encoded value:    0x02d204000000000000
        // encoded document: 0x02, 0xd2, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4e, 0x4f, 0x52, 0x54
        //                 | tag | 64 bit int ---------------------------------- | NORT trailer --------- |
        let data: [u8; _] = [
            0x02, 0xd2, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4e, 0x4f, 0x52, 0x54,
        ];
        let doc = ScalarDocument::new(&data).unwrap();
        assert_eq!(doc.value, ValueType::I64(1234));

        // Value{Type: tron.TypeF64, F64: 1.5}
        // encoded value:    0x03000000000000f83f
        // encoded document: 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf8, 0x3f, 0x4e, 0x4f, 0x52, 0x54
        //                 | tag | 64 bit float -------------------------------- | NORT trailer --------- |
        let data: [u8; _] = [
            0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf8, 0x3f, 0x4e, 0x4f, 0x52, 0x54,
        ];
        let doc = ScalarDocument::new(&data).unwrap();
        assert_eq!(doc.value, ValueType::F64(1.5));

        // Value{Type: tron.TypeTxt, Bytes: []byte("hi")}
        // encoded value:    0x2C6869
        // encoded document: 0x2C, 0x68, 0x69, 0x4e, 0x4f, 0x52, 0x54
        //                 | tag | 2 bytes  | NORT trailer --------- |
        let data: [u8; _] = [0x2C, 0x68, 0x69, 0x4e, 0x4f, 0x52, 0x54];
        let doc = ScalarDocument::new(&data).unwrap();
        assert_eq!(doc.value, ValueType::Txt("hi"));

        // Value{Type: tron.TypeBin, Bytes: []byte{255, 255}}
        // encoded value:    0x2Dffff
        // encoded document: 0x2D, 0xff, 0xff, 0x4e, 0x4f, 0x52, 0x54
        //                 | tag | 2 bytes  | NORT trailer --------- |
        let data: [u8; _] = [0x2D, 0xff, 0xff, 0x4e, 0x4f, 0x52, 0x54];
        let doc = ScalarDocument::new(&data).unwrap();
        assert_eq!(doc.value, ValueType::Bin(&[0xff, 0xff]));

        // TODO: should we be able to encode a scalar document from an arr?
        // Value{Type: tron.TypeArr, Offset: 32}
        // encoded value:    0x0620
        // encoded document: 0x06, 0x20, 0x4e, 0x4f, 0x52, 0x54
        //                 | tag | int | NORT trailer --------- |
        let data: [u8; _] = [0x06, 0x20, 0x4e, 0x4f, 0x52, 0x54];
        let doc = ScalarDocument::new(&data).unwrap();
        assert_eq!(doc.value, ValueType::Arr(32));

        // TODO: should we be able to encode a scalar document from a map?
        // Value{Type: tron.TypeMap, Offset: 3836502546}
        // encoded value:    0x1f1262ace4
        // encoded document: 0x1f, 0x12, 0x62, 0xac, 0xe4, 0x4e, 0x4f, 0x52, 0x54
        //                 | tag | uint 32 -------------- | NORT trailer --------- |
        let data: [u8; _] = [0x1f, 0x12, 0x62, 0xac, 0xe4, 0x4e, 0x4f, 0x52, 0x54];
        let doc = ScalarDocument::new(&data).unwrap();
        assert_eq!(doc.value, ValueType::Map(3836502546));
    }

    #[test]
    fn parse_nil() {
        let data = [0x00, b'N', b'O', b'R', b'T'];
        let doc = ScalarDocument::new(&data).unwrap();
        assert_eq!(doc.value, ValueType::Nil);
    }

    #[test]
    fn parse_bit_false() {
        let data = [0x01, b'N', b'O', b'R', b'T'];
        let doc = ScalarDocument::new(&data).unwrap();
        assert_eq!(doc.value, ValueType::Bit(false));
    }

    #[test]
    fn parse_bit_true() {
        let data = [0x09, b'N', b'O', b'R', b'T'];
        let doc = ScalarDocument::new(&data).unwrap();
        assert_eq!(doc.value, ValueType::Bit(true));
    }

    #[test]
    fn parse_i64() {
        let data = [
            0x02, // tag
            0xD2, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // 1234 little-endian
            b'N', b'O', b'R', b'T',
        ];
        let doc = ScalarDocument::new(&data).unwrap();
        assert_eq!(doc.value, ValueType::I64(1234));
    }

    #[test]
    fn parse_f64() {
        let data = [
            0x03, // tag
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xF8, 0x3F, // 1.5 little-endian
            b'N', b'O', b'R', b'T',
        ];
        let doc = ScalarDocument::new(&data).unwrap();
        assert_eq!(doc.value, ValueType::F64(1.5));
    }

    #[test]
    fn parse_txt_packed() {
        let data = [
            0x2C, // tag: txt, packed, len=2
            0x68, 0x69, // "hi"
            b'N', b'O', b'R', b'T',
        ];
        let doc = ScalarDocument::new(&data).unwrap();
        assert_eq!(doc.value, ValueType::Txt("hi"));
    }

    #[test]
    fn parse_txt_empty() {
        let data = [
            0x0C, // tag: txt, packed, len=0
            b'N', b'O', b'R', b'T',
        ];
        let doc = ScalarDocument::new(&data).unwrap();
        assert_eq!(doc.value, ValueType::Txt(""));
    }

    #[test]
    fn parse_txt_unpacked() {
        // 16-char string (can't fit in packed 0-15)
        let data = [
            0x14, // tag: txt, unpacked, N=1 byte for length
            0x10, // length: 16
            0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, // "01234567"
            0x38, 0x39, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, // "89abcdef"
            b'N', b'O', b'R', b'T',
        ];
        let doc = ScalarDocument::new(&data).unwrap();
        assert_eq!(doc.value, ValueType::Txt("0123456789abcdef"));
    }

    #[test]
    fn parse_bin_packed() {
        let data = [
            0x3D, // tag: bin, packed, len=3
            0xAA, 0xBB, 0xCC, // payload
            b'N', b'O', b'R', b'T',
        ];
        let doc = ScalarDocument::new(&data).unwrap();
        assert_eq!(doc.value, ValueType::Bin(&[0xAA, 0xBB, 0xCC]));
    }

    #[test]
    fn rejects_too_short() {
        // Less than 5 bytes
        let data = [0x00, b'N', b'O', b'R'];
        assert_eq!(ScalarDocument::new(&data), None);
    }

    #[test]
    fn rejects_wrong_magic() {
        let data = [0x00, b'T', b'R', b'O', b'N']; // TRON instead of NORT
        assert_eq!(ScalarDocument::new(&data), None);
    }

    #[test]
    fn rejects_extra_bytes_before_terminator() {
        let data = [
            0x00, // nil
            0xFF, // extra garbage byte
            b'N', b'O', b'R', b'T',
        ];
        assert_eq!(ScalarDocument::new(&data), None);
    }

    #[test]
    fn rejects_truncated_value() {
        // i64 needs 9 bytes but only 5 provided before NORT
        let data = [
            0x40, // i64 tag
            0x01, 0x02, 0x03, 0x04, // only 4 bytes of payload
            b'N', b'O', b'R', b'T',
        ];
        assert_eq!(ScalarDocument::new(&data), None);
    }
}
