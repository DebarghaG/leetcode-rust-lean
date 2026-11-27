pub fn xor_game(nums: &[i64]) -> bool {
    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < nums.len() {
        total = total ^ nums[i];
        i += 1;
    }

    total == 0 || nums.len() % 2 == 0
}
