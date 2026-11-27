pub fn mincost_tickets(days: &[i64], costs: &[i64]) -> i64 {
    let n: usize = days.len();
    let mut dp: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i <= n {
        dp.push(0);
        i += 1;
    }

    i = 1;
    while i <= n {
        let d: i64 = days[i - 1];

        let mut best: i64 = dp[i - 1] + costs[0];

        let mut j: usize = 0;
        while j < i && days[j] < d - 6 {
            j += 1;
        }
        let cand7: i64 = dp[j] + costs[1];
        if cand7 < best {
            best = cand7;
        }

        j = 0;
        while j < i && days[j] < d - 29 {
            j += 1;
        }
        let cand30: i64 = dp[j] + costs[2];
        if cand30 < best {
            best = cand30;
        }

        dp[i] = best;
        i += 1;
    }

    dp[n]
}
