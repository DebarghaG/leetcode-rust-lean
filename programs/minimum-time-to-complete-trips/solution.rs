pub fn minimum_time(time: &[i64], totalTrips: i64) -> i64 {
    let n = time.len();

    let mut min_time = time[0];
    let mut i = 1;
    while i < n {
        if time[i] < min_time {
            min_time = time[i];
        }
        i += 1;
    }

    let mut lo: i64 = 0;
    let mut hi: i64 = min_time * totalTrips;

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if enough_trips(time, mid, totalTrips) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo
}

fn enough_trips(time: &[i64], t: i64, totalTrips: i64) -> bool {
    let mut trips: i64 = 0;
    let n = time.len();
    let mut i = 0;

    while i < n {
        trips += t / time[i];
        if trips >= totalTrips {
            return true;
        }
        i += 1;
    }

    false
}
