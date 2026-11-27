pub fn count_good_substrings(s: &[u8]) -> i64 {
    let n = s.len();
    if n < 3 {
        return 0;
    }

    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i + 2 < n {
        if s[i] != s[i + 1] && s[i] != s[i + 2] && s[i + 1] != s[i + 2] {
            count += 1;
        }
        i += 1;
    }

    count
}
