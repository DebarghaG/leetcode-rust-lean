pub fn min_operations(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut ans: i64 = 0;
    let mut i: usize = 1;

    while i < n {
        if nums[i] != nums[i - 1] {
            ans += 1;
        }
        i += 1;
    }

    ans
}
