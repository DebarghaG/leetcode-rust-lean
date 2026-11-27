pub fn max_depth(s: &[u8]) -> i64 {
    let n = s.len();
    let mut depth: i64 = 0;
    let mut max_d: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let c = s[i];
        if c == b'(' {
            depth += 1;
            if depth > max_d {
                max_d = depth;
            }
        } else if c == b')' {
            depth -= 1;
        }
        i += 1;
    }

    max_d
}
