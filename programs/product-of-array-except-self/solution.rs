pub fn product_except_self(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    let mut ans: Vec<i64> = Vec::new();

    let mut prefix: i64 = 1;
    let mut i: usize = 0;
    while i < n {
        ans.push(prefix);
        prefix = prefix * nums[i];
        i = i + 1;
    }

    let mut suffix: i64 = 1;
    let mut j: usize = n;
    while j > 0 {
        j = j - 1;
        ans[j] = ans[j] * suffix;
        suffix = suffix * nums[j];
    }

    ans
}
