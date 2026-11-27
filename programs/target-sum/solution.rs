pub fn find_target_sum_ways(nums: &[i64], target: i64) -> i64 {
    let n = nums.len();

    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        sum = sum + nums[i];
        i += 1;
    }

    let mut abs_target = target;
    if abs_target < 0 {
        abs_target = -abs_target;
    }

    if abs_target > sum {
        return 0;
    }

    if (sum + target) % 2 != 0 {
        return 0;
    }

    let p_i64 = (sum + target) / 2;
    if p_i64 < 0 {
        return 0;
    }

    let p = p_i64 as usize;

    let mut dp: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j <= p {
        dp.push(0);
        j += 1;
    }

    dp[0] = 1;

    let mut idx: usize = 0;
    while idx < n {
        let x = nums[idx];
        if x >= 0 {
            let xu = x as usize;
            if xu <= p {
                let mut s = p + 1;
                while s > 0 {
                    s -= 1;
                    if s >= xu {
                        dp[s] = dp[s] + dp[s - xu];
                    }
                }
            }
        }
        idx += 1;
    }

    dp[p]
}
