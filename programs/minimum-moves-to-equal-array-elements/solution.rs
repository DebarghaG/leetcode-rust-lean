pub fn min_moves(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut sum: i64 = 0;
    let mut min_value: i64 = nums[0];

    let mut i: usize = 0;
    while i < n {
        let value = nums[i];
        sum += value;
        if value < min_value {
            min_value = value;
        }
        i += 1;
    }

    let n_i64 = n as i64;
    sum - n_i64 * min_value
}
