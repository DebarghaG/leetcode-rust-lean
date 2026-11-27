pub fn maximum_tastiness(price: &[i64], k: i64) -> i64 {
    let n = price.len();
    if n == 0 {
        return 0;
    }

    let mut sorted: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        sorted.push(price[i]);
        i += 1;
    }
    sorted.sort();

    let max_diff: i64 = sorted[n - 1] - sorted[0];

    let mut lo: i64 = 0;
    let mut hi: i64 = max_diff + 1;

    while lo + 1 < hi {
        let mid: i64 = lo + (hi - lo) / 2;
        if can_make(&sorted, k, mid) {
            lo = mid;
        } else {
            hi = mid;
        }
    }

    lo
}

fn can_make(sorted: &[i64], k: i64, d: i64) -> bool {
    let n = sorted.len();

    if k <= 1 {
        return true;
    }

    let mut count: i64 = 1;
    let mut last: i64 = sorted[0];
    let mut i: usize = 1;

    while i < n {
        if sorted[i] - last >= d {
            count += 1;
            last = sorted[i];

            if count >= k {
                return true;
            }
        }
        i += 1;
    }

    count >= k
}
