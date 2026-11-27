pub fn max_value(n: i64, index: i64, maxSum: i64) -> i64 {
    let mut lo: i64 = 1;
    let mut hi: i64 = maxSum;

    while lo < hi {
        let mid: i64 = lo + (hi - lo + 1) / 2;

        if minimal_sum(n, index, mid) <= maxSum {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }

    lo
}

fn side_sum(x: i64, k: i64) -> i64 {
    if k <= 0 {
        return 0;
    }

    if x > k {
        k * (2 * x - k - 1) / 2
    } else {
        x * (x - 1) / 2 + (k - x + 1)
    }
}

fn minimal_sum(n: i64, index: i64, x: i64) -> i64 {
    let left: i64 = side_sum(x, index);
    let right: i64 = side_sum(x, n - index - 1);

    x + left + right
}
