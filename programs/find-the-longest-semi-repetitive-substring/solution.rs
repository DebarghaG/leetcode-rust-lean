pub fn longest_semi_repetitive_substring(s: &[u8]) -> i64 {
    let n = s.len();
    let mut best: i64 = 0;
    let mut start: usize = 0;

    while start < n {
        let mut end: usize = start;
        let mut len: i64 = 0;
        let mut repeated_pairs: i64 = 0;

        while end < n {
            if end > start {
                if s[end] == s[end - 1] {
                    repeated_pairs += 1;
                }
            }

            len += 1;
            if repeated_pairs <= 1 {
                if len > best {
                    best = len;
                }
            }

            end += 1;
        }

        start += 1;
    }

    best
}
