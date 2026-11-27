pub fn min_increment_operations(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n < 3 {
        return 0;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < n {
        let mut cost: i64 = 0;
        if nums[i] < k {
            cost = k - nums[i];
        }

        if i < 3 {
            dp.push(cost);
        } else {
            let mut best = dp[i - 1];
            if dp[i - 2] < best {
                best = dp[i - 2];
            }
            if dp[i - 3] < best {
                best = dp[i - 3];
            }
            dp.push(cost + best);
        }

        i += 1;
    }

    let mut ans = dp[n - 1];
    if dp[n - 2] < ans {
        ans = dp[n - 2];
    }
    if dp[n - 3] < ans {
        ans = dp[n - 3];
    }

    ans
}
