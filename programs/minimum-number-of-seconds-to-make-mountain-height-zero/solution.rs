fn can_make(height: i64, worker_times: &[i64], time: i64) -> bool {
    let n = worker_times.len();
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let w = worker_times[i];

        let mut lo: i64 = 0;
        let mut hi: i64 = height;

        while lo < hi {
            let mid: i64 = (lo + hi + 1) / 2;
            let cost: i64 = w * mid * (mid + 1) / 2;

            if cost <= time {
                lo = mid;
            } else {
                hi = mid - 1;
            }
        }

        total += lo;
        if total >= height {
            return true;
        }

        i += 1;
    }

    false
}

pub fn min_number_of_seconds(mountainHeight: i64, workerTimes: &[i64]) -> i64 {
    let n = workerTimes.len();

    let mut max_w: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let w = workerTimes[i];
        if w > max_w {
            max_w = w;
        }
        i += 1;
    }

    if max_w == 0 {
        return 0;
    }

    let triangle: i64 = mountainHeight * (mountainHeight + 1) / 2;
    let mut lo: i64 = 0;
    let mut hi: i64 = max_w * triangle;

    while lo < hi {
        let mid: i64 = (lo + hi) / 2;

        if can_make(mountainHeight, workerTimes, mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo
}
