pub fn length_of_lis(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        dp.push(1);
        i += 1;
    }

    i = 1;
    while i < n {
        let mut j: usize = 0;
        while j < i {
            if nums[j] < nums[i] && dp[j] + 1 > dp[i] {
                dp[i] = dp[j] + 1;
            }
            j += 1;
        }
        i += 1;
    }

    let mut best: i64 = dp[0];
    i = 1;
    while i < n {
        if dp[i] > best {
            best = dp[i];
        }
        i += 1;
    }

    best
}
