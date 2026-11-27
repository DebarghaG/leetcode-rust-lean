pub fn find_unsorted_subarray(nums: &[i64]) -> i64 {
    let n = nums.len();

    if n <= 1 {
        return 0;
    }

    let mut left: usize = 0;
    while left + 1 < n && nums[left] <= nums[left + 1] {
        left += 1;
    }

    if left + 1 == n {
        return 0;
    }

    let mut right: usize = n - 1;
    while right > 0 && nums[right - 1] <= nums[right] {
        right -= 1;
    }

    let mut min_val = nums[left];
    let mut max_val = nums[left];

    let mut i = left + 1;
    while i <= right {
        if nums[i] < min_val {
            min_val = nums[i];
        }
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i += 1;
    }

    let mut l: usize = 0;
    while l < left && nums[l] <= min_val {
        l += 1;
    }

    let mut r: usize = n - 1;
    while r > right && nums[r] >= max_val {
        r -= 1;
    }

    (r - l + 1) as i64
}
