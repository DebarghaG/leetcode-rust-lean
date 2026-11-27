pub fn incremovable_subarray_count(nums: &[i64]) -> i64 {
    let n = nums.len();

    // pref[k] == 1  <=>  nums[0..k] (first k elements) is strictly increasing.
    let mut pref: Vec<i64> = Vec::new();
    pref.push(1); // pref[0] : empty prefix
    if n >= 1 {
        pref.push(1); // pref[1] : single element prefix
    }
    let mut k: usize = 2;
    while k <= n {
        let mut good: i64 = 0;
        if pref[k - 1] == 1 && nums[k - 1] > nums[k - 2] {
            good = 1;
        }
        pref.push(good);
        k += 1;
    }

    // suf_rev[j] corresponds to suf[n - j], where
    // suf[t] == 1  <=>  nums[t..n] is strictly increasing.
    let mut suf_rev: Vec<i64> = Vec::new();
    suf_rev.push(1); // suf[n] : empty suffix
    let mut j: usize = 1;
    while j <= n {
        let mut good: i64 = 0;
        if j == 1 {
            good = 1; // suf[n-1] : single element suffix
        } else {
            if suf_rev[j - 1] == 1 && nums[n - j] < nums[n - j + 1] {
                good = 1;
            }
        }
        suf_rev.push(good);
        j += 1;
    }

    let mut count: i64 = 0;
    let mut left: usize = 0;
    while left < n {
        let mut right: usize = left;
        while right < n {
            let mut ok: bool = true;

            // prefix part nums[0..left] must be strictly increasing
            if pref[left] != 1 {
                ok = false;
            }
            // suffix part nums[right+1..n] must be strictly increasing
            if suf_rev[n - 1 - right] != 1 {
                ok = false;
            }
            // cross boundary between the two remaining parts
            if left >= 1 && right + 1 < n {
                if nums[right + 1] <= nums[left - 1] {
                    ok = false;
                }
            }

            if ok {
                count += 1;
            }
            right += 1;
        }
        left += 1;
    }

    count
}
