fn can_eat(hens: &[i64], grains: &[i64], t: i64) -> bool {
    let n = hens.len();
    let m = grains.len();
    let mut j: usize = 0;
    let mut i: usize = 0;

    while i < n && j < m {
        let h = hens[i];
        let g = grains[j];

        if h < g {
            let reach = h + t;
            while j < m && grains[j] <= reach {
                j += 1;
            }
        } else {
            let d = h - g;
            if d > t {
                return false;
            }

            let reach_left_first = t - h + 2 * g;
            let reach_right_first = (t + h + g) / 2;
            let mut reach = reach_left_first;
            if reach_right_first > reach {
                reach = reach_right_first;
            }

            while j < m && grains[j] <= reach {
                j += 1;
            }
        }

        i += 1;
    }

    j >= m
}

pub fn minimum_time(hens: &[i64], grains: &[i64]) -> i64 {
    let n = hens.len();
    let m = grains.len();

    if m == 0 {
        return 0;
    }

    let mut hs: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        hs.push(hens[i]);
        i += 1;
    }

    let mut gs: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < m {
        gs.push(grains[j]);
        j += 1;
    }

    hs.sort();
    gs.sort();

    let left = gs[0];
    let right = gs[m - 1];
    let first_hen = hs[0];

    let mut upper = right - left;
    if first_hen > left {
        upper += first_hen - left;
    } else {
        upper += left - first_hen;
    }

    let mut lo: i64 = 0;
    let mut hi: i64 = upper;

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if can_eat(&hs, &gs, mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo
}
