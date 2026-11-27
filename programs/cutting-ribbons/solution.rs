pub fn max_length(ribbons: &[i64], k: i64) -> i64 {
    let n = ribbons.len();

    let mut max_ribbon: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if ribbons[i] > max_ribbon {
            max_ribbon = ribbons[i];
        }
        i += 1;
    }

    let mut lo: i64 = 0;
    let mut hi: i64 = max_ribbon + 1;

    while lo + 1 < hi {
        let mid: i64 = lo + (hi - lo) / 2;

        let mut total: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            total += ribbons[j] / mid;
            j += 1;
        }

        if total >= k {
            lo = mid;
        } else {
            hi = mid;
        }
    }

    lo
}
