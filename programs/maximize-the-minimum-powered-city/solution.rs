pub fn max_power(stations: &[i64], r: i64, k: i64) -> i64 {
    let n: usize = stations.len();
    if n == 0 {
        return 0;
    }
    let n_i: i64 = n as i64;

    // Build the initial power of every city using a difference array.
    let mut diff: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z <= n {
        diff.push(0);
        z += 1;
    }

    let mut i: usize = 0;
    while i < n {
        let center: i64 = i as i64;
        let mut left_i: i64 = center - r;
        if left_i < 0 {
            left_i = 0;
        }
        let mut right_i: i64 = center + r;
        if right_i > n_i - 1 {
            right_i = n_i - 1;
        }

        let left: usize = left_i as usize;
        let right: usize = right_i as usize;
        let val: i64 = stations[i];

        diff[left] += val;
        diff[right + 1] -= val;

        i += 1;
    }

    let mut base: Vec<i64> = Vec::new();
    let mut running: i64 = 0;
    i = 0;
    while i < n {
        running += diff[i];
        base.push(running);
        i += 1;
    }

    let mut total: i64 = 0;
    i = 0;
    while i < n {
        total += stations[i];
        i += 1;
    }

    let mut lo: i64 = 0;
    let mut hi: i64 = total + k + 1;

    while lo + 1 < hi {
        let mid: i64 = lo + (hi - lo) / 2;
        if can_reach(&base, r, k, mid) {
            lo = mid;
        } else {
            hi = mid;
        }
    }

    lo
}

fn can_reach(base: &[i64], r: i64, k: i64, target: i64) -> bool {
    let n: usize = base.len();
    let n_i: i64 = n as i64;

    let mut expire: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z <= n {
        expire.push(0);
        z += 1;
    }

    let mut active: i64 = 0;
    let mut used: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        active += expire[i];
        let cur: i64 = base[i] + active;

        if cur < target {
            let need: i64 = target - cur;
            used += need;
            if used > k {
                return false;
            }

            active += need;

            let i_i: i64 = i as i64;
            let mut pos: i64 = i_i + r;
            if pos > n_i - 1 {
                pos = n_i - 1;
            }

            let mut end: i64 = pos + r;
            if end > n_i - 1 {
                end = n_i - 1;
            }

            let end_idx: usize = end as usize;
            if end_idx + 1 < n {
                expire[end_idx + 1] -= need;
            }
        }

        i += 1;
    }

    true
}
