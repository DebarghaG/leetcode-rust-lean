fn can_make(s: &[u8], num_ops: i64, k: i64) -> bool {
    let n = s.len();

    if k == 1 {
        let mut diff0: i64 = 0;
        let mut diff1: i64 = 0;
        let mut i: usize = 0;

        while i < n {
            let expected0: u8 = if i % 2 == 0 { b'0' } else { b'1' };

            if s[i] == expected0 {
                diff1 += 1;
            } else {
                diff0 += 1;
            }

            i += 1;
        }

        let best = if diff0 < diff1 { diff0 } else { diff1 };
        return best <= num_ops;
    }

    let denom = k + 1;
    let mut flips: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i + 1;

        while j < n && s[j] == s[i] {
            j += 1;
        }

        let run_len = (j - i) as i64;
        flips += run_len / denom;

        if flips > num_ops {
            return false;
        }

        i = j;
    }

    flips <= num_ops
}

pub fn min_length(s: &[u8], numOps: i64) -> i64 {
    let n = s.len();

    if n == 0 {
        return 0;
    }

    let mut lo: i64 = 1;
    let mut hi: i64 = n as i64;

    while lo < hi {
        let mid = lo + (hi - lo) / 2;

        if can_make(s, numOps, mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo
}
