pub fn valid_partition(nums: &[i64]) -> bool {
    let n = nums.len();

    let mut dp: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k <= n {
        dp.push(0);
        k += 1;
    }

    dp[0] = 1;

    let mut i: usize = 1;
    while i <= n {
        if i >= 2 {
            if nums[i - 1] == nums[i - 2] {
                if dp[i - 2] == 1 {
                    dp[i] = 1;
                }
            }
        }

        if i >= 3 {
            if dp[i - 3] == 1 {
                if nums[i - 1] == nums[i - 2] {
                    if nums[i - 2] == nums[i - 3] {
                        dp[i] = 1;
                    }
                }

                if nums[i - 1] == nums[i - 2] + 1 {
                    if nums[i - 2] == nums[i - 3] + 1 {
                        dp[i] = 1;
                    }
                }
            }
        }

        i += 1;
    }

    dp[n] == 1
}
