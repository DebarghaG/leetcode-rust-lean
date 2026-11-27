pub fn minimum_steps(s: &[u8]) -> i64 {
    let mut ones: i64 = 0;
    let mut steps: i64 = 0;
    let n = s.len();
    let mut i: usize = 0;

    while i < n {
        if s[i] == b'1' {
            ones += 1;
        } else {
            steps += ones;
        }
        i += 1;
    }

    steps
}
