pub fn can_alice_win(nums: &[i64]) -> bool {
    let mut single_sum: i64 = 0;
    let mut double_sum: i64 = 0;

    let mut i: usize = 0;
    while i < nums.len() {
        if nums[i] < 10 {
            single_sum += nums[i];
        } else {
            double_sum += nums[i];
        }
        i += 1;
    }

    single_sum > double_sum || double_sum > single_sum
}
