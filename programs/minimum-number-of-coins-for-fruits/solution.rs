pub fn minimum_coins(prices: &[i64]) -> i64 {
    let n = prices.len();

    // dp[i] = minimum coins needed to acquire the first i fruits.
    let mut dp: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k <= n {
        dp.push(0);
        k += 1;
    }

    let mut i: usize = 1;
    while i <= n {
        let mut best: i64 = 1000000000000000000;
        let mut j: usize = 0;

        while j < i {
            // If fruit j is purchased, it can cover fruits up to index 2*j + 1.
            // Thus the first i fruits are covered exactly when i <= 2*j + 2.
            if i <= 2 * j + 2 {
                let candidate = dp[j] + prices[j];
                if candidate < best {
                    best = candidate;
                }
            }
            j += 1;
        }

        dp[i] = best;
        i += 1;
    }

    dp[n]
}
