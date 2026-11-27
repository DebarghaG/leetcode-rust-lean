pub fn reverse_bits(n: i64) -> i64 {
    let mut x: i64 = n & 0xFFFFFFFF;
    let mut result: i64 = 0;
    let mut i: usize = 0;

    while i < 32 {
        result = (result << 1) | (x & 1);
        x = x >> 1;
        i += 1;
    }

    result
}
