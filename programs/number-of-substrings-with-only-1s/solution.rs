pub fn num_sub(s: &[u8]) -> i64 {
    let n = s.len();
    let mut total: i64 = 0;
    let mut run: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        if s[i] == b'1' {
            run += 1;
        } else {
            if run > 0 {
                total = (total + run * (run + 1) / 2) % 1000000007;
                run = 0;
            }
        }
        i += 1;
    }

    if run > 0 {
        total = (total + run * (run + 1) / 2) % 1000000007;
    }

    total
}
