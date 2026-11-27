pub fn max_power(s: &[u8]) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    let mut best: i64 = 1;
    let mut cur: i64 = 1;
    let mut i: usize = 1;

    while i < n {
        if s[i] == s[i - 1] {
            cur += 1;
        } else {
            cur = 1;
        }

        if cur > best {
            best = cur;
        }

        i += 1;
    }

    best
}
