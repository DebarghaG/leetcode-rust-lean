pub fn number_of_arithmetic_slices(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n < 3 {
        return 0;
    }

    let mut total: i64 = 0;
    let mut current: i64 = 0;
    let mut i: usize = 2;

    while i < n {
        let diff1 = nums[i] - nums[i - 1];
        let diff2 = nums[i - 1] - nums[i - 2];

        if diff1 == diff2 {
            current = current + 1;
            total = total + current;
        } else {
            current = 0;
        }

        i += 1;
    }

    total
}
