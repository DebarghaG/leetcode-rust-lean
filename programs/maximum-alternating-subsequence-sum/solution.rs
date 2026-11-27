pub fn max_alternating_sum(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut ans = nums[0];
    let mut i: usize = 1;

    while i < n {
        let diff = nums[i] - nums[i - 1];
        if diff > 0 {
            ans += diff;
        }
        i += 1;
    }

    ans
}
