pub fn maximum_length(nums: &[i64], k: i64) -> i64 {
    let k_usize = k as usize;
    let n = nums.len();
    let mut ans: i64 = 0;

    let mut target: usize = 0;
    while target < k_usize {
        let target_i64 = target as i64;

        let mut dp: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < k_usize {
            dp.push(0);
            i += 1;
        }

        let mut idx: usize = 0;
        while idx < n {
            let r = nums[idx] % k;
            let p = (target_i64 - r + k) % k;

            let r_idx = r as usize;
            let p_idx = p as usize;

            let candidate = dp[p_idx] + 1;
            if candidate > dp[r_idx] {
                dp[r_idx] = candidate;
            }

            idx += 1;
        }

        let mut j: usize = 0;
        while j < k_usize {
            if dp[j] > ans {
                ans = dp[j];
            }
            j += 1;
        }

        target += 1;
    }

    ans
}
