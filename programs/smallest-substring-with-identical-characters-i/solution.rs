pub fn min_length(s: &[u8], numOps: i64) -> i64 {
    let n_usize = s.len();
    if n_usize == 0 {
        return 0;
    }

    let n = n_usize as i64;
    let mut lo: i64 = 1;
    let mut hi: i64 = n;

    while lo < hi {
        let mid: i64 = lo + (hi - lo) / 2;
        if can_achieve(s, mid, numOps) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo
}

fn can_achieve(s: &[u8], k: i64, num_ops: i64) -> bool {
    let n = s.len();

    if k == 1 {
        let mut mismatches_start_zero: i64 = 0;
        let mut expect_zero: bool = true;
        let mut i: usize = 0;

        while i < n {
            let expected: u8 = if expect_zero { b'0' } else { b'1' };
            if s[i] != expected {
                mismatches_start_zero += 1;
            }
            expect_zero = !expect_zero;
            i += 1;
        }

        let total = n as i64;
        let mismatches_start_one = total - mismatches_start_zero;
        let ops = if mismatches_start_zero < mismatches_start_one {
            mismatches_start_zero
        } else {
            mismatches_start_one
        };

        return ops <= num_ops;
    }

    let mut ops: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i + 1;
        while j < n && s[j] == s[i] {
            j += 1;
        }

        let len = (j - i) as i64;
        ops += len / (k + 1);

        if ops > num_ops {
            return false;
        }

        i = j;
    }

    ops <= num_ops
}
