pub fn is_one_bit_character(bits: &[i64]) -> bool {
    let n = bits.len();
    let mut i: usize = 0;

    while i + 1 < n {
        if bits[i] == 0 {
            i += 1;
        } else {
            i += 2;
        }
    }

    i + 1 == n
}
