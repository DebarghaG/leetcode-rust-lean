pub fn min_swaps(s: &[u8]) -> i64 {
    let n: usize = s.len();

    let mut zeros: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if s[i] == b'0' {
            zeros += 1;
        }
        i += 1;
    }

    let n_i64: i64 = n as i64;

    let mut mismatch_start0: i64 = 0;
    i = 0;
    while i < n {
        let expected: u8 = if i % 2 == 0 { b'0' } else { b'1' };
        if s[i] != expected {
            mismatch_start0 += 1;
        }
        i += 1;
    }

    let mismatch_start1: i64 = n_i64 - mismatch_start0;
    let mut best: i64 = -1;

    if zeros == (n_i64 + 1) / 2 {
        let ans: i64 = mismatch_start0 / 2;
        best = ans;
    }

    if zeros == n_i64 / 2 {
        let ans: i64 = mismatch_start1 / 2;
        if best == -1 || ans < best {
            best = ans;
        }
    }

    best
}
