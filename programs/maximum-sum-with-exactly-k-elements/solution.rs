pub fn maximize_sum(nums: &[i64], k: i64) -> i64 {
    let mut max_val: i64 = nums[0];
    let mut i: usize = 1;
    while i < nums.len() {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i += 1;
    }

    let mut score: i64 = 0;
    let mut step: i64 = 0;
    while step < k {
        score += max_val + step;
        step += 1;
    }

    score
}
