pub fn min_flips(s: &[u8]) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    let n_i64 = n as i64;

    // mismatches compared with the pattern starting with '0':
    // 0, 1, 0, 1, ...
    let mut mism0: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let expected: u8 = if i % 2 == 0 { b'0' } else { b'1' };
        if s[i] != expected {
            mism0 += 1;
        }
        i += 1;
    }

    let mut best: i64 = mism0;
    let other = n_i64 - mism0;
    if other < best {
        best = other;
    }

    let odd_length = n % 2 == 1;
    let mut k: usize = 1;

    while k < n {
        let first_mism: i64 = if s[k - 1] != b'0' { 1 } else { 0 };

        if odd_length {
            mism0 = n_i64 - 1 - mism0 + 2 * first_mism;
        } else {
            mism0 = n_i64 - mism0;
        }

        if mism0 < best {
            best = mism0;
        }

        let other_now = n_i64 - mism0;
        if other_now < best {
            best = other_now;
        }

        k += 1;
    }

    best
}
