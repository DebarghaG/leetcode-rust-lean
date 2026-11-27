pub fn min_cost(nums: &[i64], k: i64) -> i64 {
    let n: usize = nums.len();
    if n == 0 {
        return 0;
    }

    // Determine a safe size for frequency buckets (values may exceed n-1).
    let mut maxv: usize = 0;
    let mut a: usize = 0;
    while a < n {
        let v: usize = nums[a] as usize;
        if v > maxv {
            maxv = v;
        }
        a += 1;
    }
    let fsize: usize = maxv + 1;

    let inf: i64 = 1_000_000_000_000_000_000;

    let mut dp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z <= n {
        dp.push(inf);
        z += 1;
    }
    dp[0] = 0;

    let mut i: usize = 0;
    while i < n {
        let mut freq: Vec<i64> = Vec::new();
        let mut t: usize = 0;
        while t < fsize {
            freq.push(0);
            t += 1;
        }

        let mut trimmed_len: i64 = 0;
        let mut j: usize = i;

        while j < n {
            let x: usize = nums[j] as usize;
            let count: i64 = freq[x];

            if count == 1 {
                trimmed_len = trimmed_len + 2;
            } else if count > 1 {
                trimmed_len = trimmed_len + 1;
            }

            freq[x] = count + 1;

            let cost: i64 = k + trimmed_len;
            let candidate: i64 = dp[i] + cost;

            if candidate < dp[j + 1] {
                dp[j + 1] = candidate;
            }

            j += 1;
        }

        i += 1;
    }

    dp[n]
}
