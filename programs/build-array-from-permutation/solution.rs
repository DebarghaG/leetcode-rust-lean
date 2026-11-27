pub fn build_array(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    let mut ans: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let idx = nums[i] as usize;
        ans.push(nums[idx]);
        i = i + 1;
    }
    ans
}
