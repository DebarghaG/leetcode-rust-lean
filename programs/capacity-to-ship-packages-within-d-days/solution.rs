pub fn ship_within_days(weights: &[i64], days: i64) -> i64 {
    let n = weights.len();
    let mut lo: i64 = 0;
    let mut hi: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let w = weights[i];
        if w > lo {
            lo = w;
        }
        hi = hi + w;
        i += 1;
    }

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if can_ship(weights, days, mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo
}

fn can_ship(weights: &[i64], days: i64, capacity: i64) -> bool {
    let mut used_days: i64 = 1;
    let mut current_load: i64 = 0;
    let mut i: usize = 0;

    while i < weights.len() {
        let w = weights[i];
        if current_load + w > capacity {
            used_days = used_days + 1;
            current_load = w;
        } else {
            current_load = current_load + w;
        }
        i += 1;
    }

    used_days <= days
}
