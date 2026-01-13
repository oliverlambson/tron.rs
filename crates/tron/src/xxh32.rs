// TODO: rather use an existing crate that has the SIMD optimisations
const PRIME1: u32 = 0x9E37_79B1;
const PRIME2: u32 = 0x85EB_CA77;
const PRIME3: u32 = 0xC2B2_AE3D;
const PRIME4: u32 = 0x27D4_EB2F;
const PRIME5: u32 = 0x1656_67B1;

/// Compute xxHash32 of the given data with the given seed.
#[must_use]
pub fn xxh32(data: &[u8], seed: u32) -> u32 {
    let mut p = 0;
    let len = data.len();

    let mut h32: u32;
    if len >= 16 {
        let mut acc1 = seed.wrapping_add(PRIME1).wrapping_add(PRIME2);
        let mut acc2 = seed.wrapping_add(PRIME2);
        let mut acc3 = seed; // seed + 0;
        let mut acc4 = seed.wrapping_sub(PRIME1);
        while len - p >= 16 {
            acc1 = round(
                acc1,
                u32::from_le_bytes([data[p], data[p + 1], data[p + 2], data[p + 3]]),
            );
            p += 4;
            acc2 = round(
                acc2,
                u32::from_le_bytes([data[p], data[p + 1], data[p + 2], data[p + 3]]),
            );
            p += 4;
            acc3 = round(
                acc3,
                u32::from_le_bytes([data[p], data[p + 1], data[p + 2], data[p + 3]]),
            );
            p += 4;
            acc4 = round(
                acc4,
                u32::from_le_bytes([data[p], data[p + 1], data[p + 2], data[p + 3]]),
            );
            p += 4;
        }
        h32 = acc1
            .rotate_left(1)
            .wrapping_add(acc2.rotate_left(7))
            .wrapping_add(acc3.rotate_left(12))
            .wrapping_add(acc4.rotate_left(18));
    } else {
        h32 = seed.wrapping_add(PRIME5);
    }

    h32 = h32.wrapping_add(len as u32);

    while len - p >= 4 {
        h32 = h32.wrapping_add(
            u32::from_le_bytes([data[p], data[p + 1], data[p + 2], data[p + 3]])
                .wrapping_mul(PRIME3),
        );
        p += 4;
        h32 = h32.rotate_left(17).wrapping_mul(PRIME4);
    }

    while p < len {
        h32 = h32.wrapping_add(u32::from(data[p]).wrapping_mul(PRIME5));
        p += 1;
        h32 = h32.rotate_left(11).wrapping_mul(PRIME1);
    }

    // avalanche
    h32 ^= h32 >> 15;
    h32 = h32.wrapping_mul(PRIME2);
    h32 ^= h32 >> 13;
    h32 = h32.wrapping_mul(PRIME3);
    h32 ^= h32 >> 16;

    h32
}

fn round(acc: u32, input: u32) -> u32 {
    acc.wrapping_add(input.wrapping_mul(PRIME2))
        .rotate_left(13)
        .wrapping_mul(PRIME1)
}

#[cfg(test)]
mod test {
    use super::*;
    use serde::Deserialize;

    fn generate_sanity_buffer(len: usize) -> Vec<u8> {
        // source: https://github.com/Cyan4973/xxHash/blob/66979328cf3f15cecdc61ea58c9f81e6071f8983/tests/sanity_test_vectors_generator.c#L201-L224
        const PRIME32: u32 = 2_654_435_761;
        const PRIME64: u64 = 11_400_714_785_074_694_797;

        let mut byte_gen: u64 = u64::from(PRIME32);
        (0..len)
            .map(|_| {
                let b = (byte_gen >> 56) as u8;
                byte_gen = byte_gen.wrapping_mul(PRIME64);
                b
            })
            .collect()
    }

    #[derive(Deserialize)]
    struct TestVectors {
        arrays: Arrays,
    }

    #[derive(Deserialize)]
    struct Arrays {
        #[serde(rename = "XSUM_XXH32_testdata")]
        xxh32_testdata: Vec<TestCase>,
    }

    #[derive(Deserialize)]
    struct TestCase {
        len: usize,
        seed: String,
        result: String,
    }

    fn parse_hex(s: &str) -> u32 {
        u32::from_str_radix(s.strip_prefix("0x").unwrap_or(s), 16).unwrap()
    }

    #[test]
    fn xxh32_sanity() {
        let json = include_str!(
            "../../../tron-shared/shared/testdata/vectors/xxhash_sanity_test_vectors.json"
        );
        let vectors: TestVectors = serde_json::from_str(json).unwrap();

        for case in &vectors.arrays.xxh32_testdata {
            let data = generate_sanity_buffer(case.len);
            let seed = parse_hex(&case.seed);
            let expected = parse_hex(&case.result);
            assert_eq!(
                xxh32(&data, seed),
                expected,
                "failed for len={}, seed={seed:#X}",
                case.len
            );
        }
    }
}
