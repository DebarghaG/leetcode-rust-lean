pub fn check_zero_ones(s: &[u8]) -> bool {
    let n = s.len();
    let mut max_ones: i64 = 0;
    let mut max_zeros: i64 = 0;
    let mut cur_ones: i64 = 0;
    let mut cur_zeros: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        if s[i] == b'1' {
            cur_ones += 1;
            cur_zeros = 0;
            if cur_ones > max_ones {
                max_ones = cur_ones;
            }
        } else {
            cur_zeros += 1;
            cur_ones = 0;
            if cur_zeros > max_zeros {
                max_zeros = cur_zeros;
            }
        }
        i += 1;
    }

    max_ones > max_zeros
}
