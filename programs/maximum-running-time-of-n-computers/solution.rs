fn can_run(n: i64, batteries: &[i64], t: i64) -> bool {
    let mut total: i64 = 0;
    let len = batteries.len();
    let mut i: usize = 0;

    while i < len {
        if batteries[i] < t {
            total += batteries[i];
        } else {
            total += t;
        }
        i += 1;
    }

    total >= n * t
}

pub fn max_run_time(n: i64, batteries: &[i64]) -> i64 {
    let mut total: i64 = 0;
    let len = batteries.len();
    let mut i: usize = 0;

    while i < len {
        total += batteries[i];
        i += 1;
    }

    let mut lo: i64 = 0;
    let mut hi: i64 = total / n;

    while lo < hi {
        let mid: i64 = lo + (hi - lo + 1) / 2;

        if can_run(n, batteries, mid) {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }

    lo
}
