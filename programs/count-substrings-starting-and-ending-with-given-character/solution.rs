pub fn count_substrings(s: &[u8], c: &[u8]) -> i64 {
    if c.len() == 0 {
        return 0;
    }

    let target = c[0];
    let mut count: i64 = 0;
    let n = s.len();
    let mut i: usize = 0;

    while i < n {
        if s[i] == target {
            count += 1;
        }
        i += 1;
    }

    count * (count + 1) / 2
}
