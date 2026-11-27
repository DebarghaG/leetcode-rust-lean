fn lnds_len(seq: &[i64]) -> i64 {
    let mut tails: Vec<i64> = Vec::new();
    let n = seq.len();
    let mut i: usize = 0;

    while i < n {
        let x = seq[i];

        let mut lo: usize = 0;
        let mut hi: usize = tails.len();

        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if tails[mid] <= x {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        if lo == tails.len() {
            tails.push(x);
        } else {
            tails[lo] = x;
        }

        i += 1;
    }

    tails.len() as i64
}

pub fn k_increasing(arr: &[i64], k: i64) -> i64 {
    let n = arr.len();

    if n == 0 || k <= 0 {
        return 0;
    }

    let step = k as usize;
    let limit = if step < n { step } else { n };

    let mut ans: i64 = 0;
    let mut r: usize = 0;

    while r < limit {
        let mut seq: Vec<i64> = Vec::new();
        let mut idx = r;

        while idx < n {
            seq.push(arr[idx]);
            idx += step;
        }

        let m = seq.len() as i64;
        let keep = lnds_len(&seq);
        ans += m - keep;

        r += 1;
    }

    ans
}
