pub fn max_operations(s: &[u8]) -> i64 {
    let mut ans: i64 = 0;
    let mut ones: i64 = 0;
    let n: usize = s.len();
    let mut i: usize = 0;

    while i < n {
        if s[i] == b'1' {
            ones += 1;
        } else {
            if i != 0 {
                if s[i - 1] == b'1' {
                    ans += ones;
                }
            }
        }
        i += 1;
    }

    ans
}
