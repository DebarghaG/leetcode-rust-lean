pub fn min_start_value(nums: &[i64]) -> i64 {
    let mut sum: i64 = 0;
    let mut min_sum: i64 = 0;

    let mut i: usize = 0;
    while i < nums.len() {
        sum += nums[i];
        if sum < min_sum {
            min_sum = sum;
        }
        i += 1;
    }

    let required: i64 = 1 - min_sum;
    if required > 1 {
        required
    } else {
        1
    }
}
