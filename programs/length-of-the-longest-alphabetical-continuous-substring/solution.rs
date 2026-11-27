pub fn longest_continuous_substring(s: &[u8]) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    let mut best: i64 = 1;
    let mut cur: i64 = 1;
    let mut i: usize = 1;

    while i < n {
        if (s[i] as i64) == (s[i - 1] as i64) + 1 {
            cur = cur + 1;
            if cur > best {
                best = cur;
            }
        } else {
            cur = 1;
        }
        i = i + 1;
    }

    best
}
