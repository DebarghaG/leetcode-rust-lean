pub fn max_score(s: &[u8]) -> i64 {
    let n = s.len();

    let mut total_ones: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if s[i] == b'1' {
            total_ones += 1;
        }
        i += 1;
    }

    let mut left_zeros: i64 = 0;
    let mut right_ones: i64 = total_ones;
    let mut best: i64 = 0;

    let mut j: usize = 0;
    while j + 1 < n {
        if s[j] == b'0' {
            left_zeros += 1;
        } else {
            right_ones -= 1;
        }

        let score = left_zeros + right_ones;
        if score > best {
            best = score;
        }

        j += 1;
    }

    best
}
