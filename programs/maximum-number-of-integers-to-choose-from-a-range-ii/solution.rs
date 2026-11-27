pub fn max_count(banned: &[i64], n: i64, maxSum: i64) -> i64 {
    let mut bs: Vec<i64> = Vec::new();
    let m = banned.len();
    let mut i: usize = 0;
    while i < m {
        let b = banned[i];
        if b >= 1 && b <= n {
            bs.push(b);
        }
        i += 1;
    }
    bs.sort();

    let mut count: i64 = 0;
    let mut remaining: i64 = maxSum;
    let mut next: i64 = 1;
    let mut idx: usize = 0;
    let blen = bs.len();

    while idx < blen {
        let b = bs[idx];

        if b >= next {
            let len = b - next;
            if len > 0 {
                let k = max_take(next, len, remaining);
                count += k;

                if k < len {
                    return count;
                }

                let used = sum_first(next, len);
                remaining -= used;
            }

            next = b + 1;
        }

        idx += 1;
    }

    if next <= n {
        let len = n - next + 1;
        let k = max_take(next, len, remaining);
        count += k;
    }

    count
}

fn sum_first(x: i64, k: i64) -> i64 {
    if k <= 0 {
        return 0;
    }
    k * (2 * x + (k - 1)) / 2
}

fn max_take(x: i64, len: i64, budget: i64) -> i64 {
    if len <= 0 {
        return 0;
    }

    let mut lo: i64 = 0;
    let mut hi: i64 = len;

    while lo < hi {
        let mid = lo + (hi - lo + 1) / 2;
        if sum_first(x, mid) <= budget {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }

    lo
}
