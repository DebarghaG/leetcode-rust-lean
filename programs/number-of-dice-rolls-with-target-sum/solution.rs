pub fn num_rolls_to_target(n: i64, k: i64, target: i64) -> i64 {
    let md: i64 = 1_000_000_007;

    if target < n {
        return 0;
    }
    if target > n * k {
        return 0;
    }

    let t: usize = target as usize;
    let n_us: usize = n as usize;
    let k_us: usize = k as usize;

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= t {
        dp.push(0);
        i += 1;
    }
    dp[0] = 1;

    let mut dice: usize = 1;
    while dice <= n_us {
        let mut next: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j <= t {
            next.push(0);
            j += 1;
        }

        let mut s: usize = 1;
        while s <= t {
            let mut ways: i64 = 0;
            let max_face: usize = if k_us < s { k_us } else { s };

            let mut f: usize = 1;
            while f <= max_face {
                ways += dp[s - f];
                if ways >= md {
                    ways -= md;
                }
                f += 1;
            }

            next[s] = ways;
            s += 1;
        }

        dp = next;
        dice += 1;
    }

    dp[t]
}
