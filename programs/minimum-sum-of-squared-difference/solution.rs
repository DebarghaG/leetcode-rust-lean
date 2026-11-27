pub fn min_sum_square_diff(nums1: &[i64], nums2: &[i64], k1: i64, k2: i64) -> i64 {
    let n = nums1.len();
    if n == 0 {
        return 0;
    }

    let mut diffs: Vec<i64> = Vec::new();
    let mut max_diff: i64 = 0;
    let mut total_diff: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let mut d = nums1[i] - nums2[i];
        if d < 0 {
            d = -d;
        }
        diffs.push(d);
        if d > max_diff {
            max_diff = d;
        }
        total_diff = total_diff + d;
        i += 1;
    }

    let k = k1 + k2;
    if total_diff <= k {
        return 0;
    }

    // Find the smallest cap level t such that reducing all differences
    // above t down to t costs at most k.
    let mut lo: i64 = 0;
    let mut hi: i64 = max_diff;

    while lo < hi {
        let mid = (lo + hi) / 2;

        let mut cost: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            let d = diffs[j];
            if d > mid {
                cost = cost + (d - mid);
            }
            j += 1;
        }

        if cost <= k {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    let t = lo;

    let mut cost_t: i64 = 0;
    let mut count_ge: i64 = 0;
    let mut ans: i64 = 0;

    let mut j: usize = 0;
    while j < n {
        let d = diffs[j];
        if d >= t {
            cost_t = cost_t + (d - t);
            count_ge = count_ge + 1;
        } else {
            ans = ans + d * d;
        }
        j += 1;
    }

    let rem = k - cost_t;
    let t2 = t * t;
    let tm2 = (t - 1) * (t - 1);

    ans = ans + (count_ge - rem) * t2 + rem * tm2;
    ans
}
