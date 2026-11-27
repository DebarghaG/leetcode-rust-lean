pub fn maximum_jumps(nums: &[i64], target: i64) -> i64 {
    let n = nums.len();

    if n == 0 {
        return -1;
    }
    if n == 1 {
        return 0;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < n {
        dp.push(-1);
        k += 1;
    }

    dp[n - 1] = 0;

    let mut i: usize = n - 1;
    while i > 0 {
        i -= 1;

        let mut best: i64 = -1;
        let mut j: usize = i + 1;

        while j < n {
            if dp[j] != -1 {
                let diff: i64 = nums[j] - nums[i];
                if diff >= -target && diff <= target {
                    let candidate: i64 = dp[j] + 1;
                    if candidate > best {
                        best = candidate;
                    }
                }
            }
            j += 1;
        }

        dp[i] = best;
    }

    dp[0]
}
