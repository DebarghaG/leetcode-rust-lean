pub fn min_changes(s: &[u8]) -> i64 {
    let n = s.len();
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i + 1 < n {
        if s[i] != s[i + 1] {
            ans += 1;
        }
        i += 2;
    }

    ans
}
