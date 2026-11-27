pub fn max_score(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut maxv: i64 = nums[n - 1];
    let mut ans: i64 = 0;
    let mut i: usize = n - 1;

    while i > 0 {
        if nums[i] > maxv {
            maxv = nums[i];
        }
        ans = ans + maxv;
        i = i - 1;
    }

    ans
}
