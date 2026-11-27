pub fn get_concatenation(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    let mut ans: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        ans.push(nums[i]);
        i += 1;
    }
    let mut j: usize = 0;
    while j < n {
        ans.push(nums[j]);
        j += 1;
    }
    ans
}
