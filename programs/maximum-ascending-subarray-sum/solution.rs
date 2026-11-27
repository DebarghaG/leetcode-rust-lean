pub fn max_ascending_sum(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut current_sum = nums[0];
    let mut best_sum = nums[0];

    let mut i = 1;
    while i < n {
        if nums[i] > nums[i - 1] {
            current_sum += nums[i];
        } else {
            current_sum = nums[i];
        }

        if current_sum > best_sum {
            best_sum = current_sum;
        }

        i += 1;
    }

    best_sum
}
