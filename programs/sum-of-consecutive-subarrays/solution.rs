pub fn get_sum(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let modulo: i64 = 1000000007;

    let mut total: i64 = nums[0] % modulo;
    let mut dp: i64 = nums[0] % modulo;
    let mut run_len: i64 = 1;
    let mut prev_diff: i64 = 0;

    let mut i: usize = 1;
    while i < n {
        let diff = nums[i] - nums[i - 1];

        if diff == 1 || diff == -1 {
            if i >= 2 && prev_diff == diff {
                run_len = run_len + 1;
                dp = (dp + (run_len * nums[i]) % modulo) % modulo;
            } else {
                run_len = 2;
                dp = (nums[i - 1] + 2 * nums[i]) % modulo;
            }
        } else {
            run_len = 1;
            dp = nums[i] % modulo;
        }

        prev_diff = diff;
        total = (total + dp) % modulo;
        i += 1;
    }

    total
}
