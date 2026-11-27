fn exists_window(a: &[i64], pref: &[i64], m: usize, k: i64) -> bool {
    let n = a.len();
    if m == 0 {
        return true;
    }
    if m > n {
        return false;
    }

    let mut l: usize = 0;
    while l + m <= n {
        let r: usize = l + m - 1;
        let mid: usize = (l + r) / 2;
        let median: i64 = a[mid];

        let left_count: i64 = (mid - l) as i64;
        let left_sum: i64 = pref[mid] - pref[l];

        let right_count: i64 = (r - mid) as i64;
        let right_sum: i64 = pref[r + 1] - pref[mid + 1];

        let cost: i64 = median * left_count - left_sum + right_sum - median * right_count;
        if cost <= k {
            return true;
        }

        l += 1;
    }

    false
}

pub fn max_frequency_score(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }
    a.sort();

    let mut pref: Vec<i64> = Vec::new();
    pref.push(0);
    let mut sum: i64 = 0;
    let mut j: usize = 0;
    while j < n {
        sum += a[j];
        pref.push(sum);
        j += 1;
    }

    let mut lo: usize = 0;
    let mut hi: usize = n;

    while lo < hi {
        let mid: usize = lo + (hi - lo + 1) / 2;
        if exists_window(&a, &pref, mid, k) {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }

    lo as i64
}
