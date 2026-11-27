pub fn min_elements(nums: &[i64], limit: i64, goal: i64) -> i64 {
    let mut sum: i64 = 0;
    let mut i: usize = 0;

    while i < nums.len() {
        sum += nums[i];
        i += 1;
    }

    let mut diff: i64 = goal - sum;
    if diff < 0 {
        diff = -diff;
    }

    if diff == 0 {
        return 0;
    }

    (diff + limit - 1) / limit
}
