pub fn left_right_difference(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total += nums[i];
        i += 1;
    }

    let mut answer: Vec<i64> = Vec::new();
    let mut left_sum: i64 = 0;

    i = 0;
    while i < n {
        let right_sum = total - left_sum - nums[i];
        let diff = left_sum - right_sum;
        let abs_diff = if diff < 0 { 0 - diff } else { diff };

        answer.push(abs_diff);
        left_sum += nums[i];
        i += 1;
    }

    answer
}
