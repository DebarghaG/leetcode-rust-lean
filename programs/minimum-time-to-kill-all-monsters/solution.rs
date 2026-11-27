pub fn minimum_time(power: &[i64]) -> i64 {
    let n: usize = power.len();
    let total: usize = 1usize << n;
    let inf: i64 = 1_000_000_000_000_000_000;

    let mut dp: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < total {
        dp.push(inf);
        idx += 1;
    }
    dp[0] = 0;

    let mut mask: usize = 0;
    while mask < total {
        if dp[mask] != inf {
            let mut temp: usize = mask;
            let mut killed: i64 = 0;
            while temp > 0 {
                if (temp & 1usize) == 1usize {
                    killed += 1;
                }
                temp = temp >> 1;
            }

            let gain: i64 = killed + 1;

            let mut i: usize = 0;
            while i < n {
                let bit: usize = 1usize << i;
                if (mask & bit) == 0 {
                    let p: i64 = power[i];
                    let days: i64 = (p + gain - 1) / gain;
                    let next_mask: usize = mask | bit;
                    let candidate: i64 = dp[mask] + days;
                    if candidate < dp[next_mask] {
                        dp[next_mask] = candidate;
                    }
                }
                i += 1;
            }
        }
        mask += 1;
    }

    dp[total - 1]
}
