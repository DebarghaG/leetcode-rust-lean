pub fn max_length_between_equal_characters(s: &[u8]) -> i64 {
    let n = s.len();
    let mut best: i64 = -1;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i + 1;
        while j < n {
            if s[i] == s[j] {
                let between: i64 = (j - i - 1) as i64;
                if between > best {
                    best = between;
                }
            }
            j += 1;
        }
        i += 1;
    }

    best
}
