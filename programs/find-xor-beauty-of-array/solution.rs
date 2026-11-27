pub fn xor_beauty(nums: &[i64]) -> i64 {
    let mut ans: i64 = 0;
    let mut i: usize = 0;
    while i < nums.len() {
        ans ^= nums[i];
        i += 1;
    }
    ans
}
