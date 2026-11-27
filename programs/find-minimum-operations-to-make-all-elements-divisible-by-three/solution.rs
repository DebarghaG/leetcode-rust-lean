pub fn minimum_operations(nums: &[i64]) -> i64 {
    let mut ans: i64 = 0;
    let mut i: usize = 0;
    while i < nums.len() {
        if nums[i] % 3 != 0 {
            ans += 1;
        }
        i += 1;
    }
    ans
}
