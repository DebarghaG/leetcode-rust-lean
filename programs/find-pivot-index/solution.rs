pub fn pivot_index(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return -1;
    }

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total += nums[i];
        i += 1;
    }

    let mut left_sum: i64 = 0;
    i = 0;
    while i < n {
        let right_sum = total - left_sum - nums[i];
        if left_sum == right_sum {
            return i as i64;
        }
        left_sum += nums[i];
        i += 1;
    }

    -1
}
