fn min_pair(num: &[u8], a: u8, b: u8) -> i64 {
    let n = num.len();
    if n < 2 {
        return 1_000_000;
    }

    let mut j: usize = n;
    let mut b_idx: usize = n;
    while j > 0 {
        j -= 1;
        if num[j] == b {
            b_idx = j;
            break;
        }
    }

    if b_idx == n {
        return 1_000_000;
    }

    let mut i: usize = b_idx;
    while i > 0 {
        i -= 1;
        if num[i] == a {
            return (n - i - 2) as i64;
        }
    }

    1_000_000
}

pub fn minimum_operations(num: &[u8]) -> i64 {
    let n = num.len();
    if n == 0 {
        return 0;
    }

    let mut all_zero: bool = true;
    let mut has_zero: bool = false;
    let mut k: usize = 0;

    while k < n {
        if num[k] == b'0' {
            has_zero = true;
        } else {
            all_zero = false;
        }
        k += 1;
    }

    if all_zero {
        return 0;
    }

    let mut best: i64 = n as i64;

    if has_zero {
        let cand_zero: i64 = (n as i64) - 1;
        if cand_zero < best {
            best = cand_zero;
        }
    }

    let mut cand: i64 = min_pair(num, b'0', b'0');
    if cand < best {
        best = cand;
    }

    cand = min_pair(num, b'2', b'5');
    if cand < best {
        best = cand;
    }

    cand = min_pair(num, b'5', b'0');
    if cand < best {
        best = cand;
    }

    cand = min_pair(num, b'7', b'5');
    if cand < best {
        best = cand;
    }

    best
}
