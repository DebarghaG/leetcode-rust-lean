pub fn split_array(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();

    let mut lo: i64 = 0;
    let mut hi: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        if nums[i] > lo {
            lo = nums[i];
        }
        hi += nums[i];
        i += 1;
    }

    while lo < hi {
        let mid = lo + (hi - lo) / 2;

        let mut parts: i64 = 1;
        let mut current_sum: i64 = 0;
        let mut j: usize = 0;

        while j < n {
            if current_sum + nums[j] > mid {
                parts += 1;
                current_sum = nums[j];
            } else {
                current_sum += nums[j];
            }
            j += 1;
        }

        if parts <= k {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo
}
