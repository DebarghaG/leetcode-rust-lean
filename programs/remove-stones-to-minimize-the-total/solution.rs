pub fn min_stone_sum(piles: &[i64], k: i64) -> i64 {
    let n = piles.len();

    let mut max_v: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let p = piles[i];
        if p > max_v {
            max_v = p;
        }
        i += 1;
    }

    let mut lo: i64 = 1;
    let mut hi: i64 = max_v;
    while lo < hi {
        let mid = (lo + hi) / 2;
        if ops_leq(piles, mid, k) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    let v = lo;

    let mut used: i64 = 0;
    let mut total: i64 = 0;

    i = 0;
    while i < n {
        let x = piles[i];
        let mut y = x;

        while y > v {
            y = y - y / 2;
            used += 1;
        }

        total += y;
        i += 1;
    }

    let rem = k - used;
    if rem > 0 {
        total -= rem * (v / 2);
    }

    total
}

fn ops_leq(piles: &[i64], v: i64, k: i64) -> bool {
    let n = piles.len();
    let mut i: usize = 0;
    let mut total: i64 = 0;

    while i < n {
        let x = piles[i];
        let mut p = v;
        let mut t: i64 = 0;

        while p < x {
            p = p * 2;
            t += 1;
        }

        total += t;
        if total > k {
            return false;
        }

        i += 1;
    }

    true
}
