pub fn sum_of_power(nums: &[i64], k: i64) -> i64 {
    const MOD: i64 = 1_000_000_007;

    let kk = k as usize;
    let mut dp: Vec<i64> = Vec::new();

    let mut i = 0;
    while i <= kk {
        dp.push(0);
        i += 1;
    }
    dp[0] = 1;

    let n = nums.len();
    let mut idx = 0;

    while idx < n {
        let x = nums[idx];
        let x_usize = if x <= k { x as usize } else { kk + 1 };

        let mut s = kk + 1;
        while s > 0 {
            s -= 1;

            let mut val = dp[s] * 2;
            if s >= x_usize {
                val += dp[s - x_usize];
            }

            dp[s] = val % MOD;
        }

        idx += 1;
    }

    dp[kk]
}
