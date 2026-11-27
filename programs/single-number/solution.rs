pub fn single_number(nums: &[i64]) -> i64 {
    let mut result: i64 = 0;
    let mut i: usize = 0;
    while i < nums.len() {
        result = result ^ nums[i];
        i += 1;
    }
    result
}
