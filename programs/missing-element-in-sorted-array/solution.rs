pub fn missing_element(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();

    if n == 0 {
        return k;
    }

    let last_missing = nums[n - 1] - nums[0] - ((n - 1) as i64);

    if k > last_missing {
        return nums[n - 1] + (k - last_missing);
    }

    let mut lo: usize = 0;
    let mut hi: usize = n - 1;

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        let missing_before_mid = nums[mid] - nums[0] - (mid as i64);

        if missing_before_mid >= k {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    if lo == 0 {
        return nums[0] + k - 1;
    }

    let prev_missing = nums[lo - 1] - nums[0] - ((lo - 1) as i64);
    nums[lo - 1] + (k - prev_missing)
}
