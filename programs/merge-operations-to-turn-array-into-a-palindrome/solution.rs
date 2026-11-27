pub fn minimum_operations(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut left: usize = 0;
    let mut right: usize = n - 1;
    let mut left_sum: i64 = nums[left];
    let mut right_sum: i64 = nums[right];
    let mut operations: i64 = 0;

    while left < right {
        if left_sum == right_sum {
            left += 1;
            right -= 1;
            if left < right {
                left_sum = nums[left];
                right_sum = nums[right];
            }
        } else if left_sum < right_sum {
            left += 1;
            left_sum += nums[left];
            operations += 1;
        } else {
            right -= 1;
            right_sum += nums[right];
            operations += 1;
        }
    }

    operations
}
