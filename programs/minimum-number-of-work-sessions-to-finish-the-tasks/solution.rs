pub fn min_sessions(tasks: &[i64], sessionTime: i64) -> i64 {
    let n = tasks.len();
    let total: usize = 1usize << n;

    let mut dp: Vec<i64> = Vec::new();
    let mut used: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < total {
        dp.push(1000000);
        used.push(0);
        i += 1;
    }

    dp[0] = 1;
    used[0] = 0;

    let mut mask: usize = 0;
    while mask < total {
        let cur_sessions = dp[mask];
        let cur_used = used[mask];

        let mut j: usize = 0;
        while j < n {
            let bit: usize = 1usize << j;
            if (mask & bit) == 0 {
                let t = tasks[j];
                let nmask = mask | bit;

                let mut new_sessions = cur_sessions;
                let mut new_used = cur_used + t;

                if new_used > sessionTime {
                    new_sessions += 1;
                    new_used = t;
                }

                if new_sessions < dp[nmask]
                    || (new_sessions == dp[nmask] && new_used < used[nmask])
                {
                    dp[nmask] = new_sessions;
                    used[nmask] = new_used;
                }
            }
            j += 1;
        }

        mask += 1;
    }

    dp[total - 1]
}
