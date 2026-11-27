pub fn min_operations(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut operations: i64 = 0;
    let mut previous: i64 = nums[0];
    let mut i: usize = 1;

    while i < n {
        let current = nums[i];

        if current <= previous {
            let target = previous + 1;
            operations += target - current;
            previous = target;
        } else {
            previous = current;
        }

        i += 1;
    }

    operations
}
