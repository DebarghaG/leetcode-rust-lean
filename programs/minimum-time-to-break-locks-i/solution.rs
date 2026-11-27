pub fn find_minimum_time(strength: &[i64], k: i64) -> i64 {
    let n = strength.len();
    let size = 1usize << n;

    let mut dp: Vec<i64> = Vec::new();
    let mut idx = 0usize;
    while idx < size {
        dp.push(1000000000000000000);
        idx += 1;
    }
    dp[0] = 0;

    let mut mask = 0usize;
    while mask < size {
        let mut broken: i64 = 0;
        let mut temp = mask;
        while temp > 0 {
            if (temp & 1usize) == 1usize {
                broken += 1;
            }
            temp = temp >> 1;
        }

        let factor = 1 + k * broken;

        let mut i = 0usize;
        while i < n {
            let bit = 1usize << i;
            if (mask & bit) == 0usize {
                let s = strength[i];
                let cost = (s + factor - 1) / factor;
                let next_mask = mask | bit;
                let candidate = dp[mask] + cost;
                if candidate < dp[next_mask] {
                    dp[next_mask] = candidate;
                }
            }
            i += 1;
        }

        mask += 1;
    }

    dp[size - 1]
}
