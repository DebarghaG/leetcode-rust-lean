pub fn maximum_xor(nums: &[i64]) -> i64 {
    let mut result: i64 = 0;
    let mut i: usize = 0;
    while i < nums.len() {
        result = result | nums[i];
        i = i + 1;
    }
    result
}
