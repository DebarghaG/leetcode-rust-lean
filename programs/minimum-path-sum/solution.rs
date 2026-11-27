pub fn min_path_sum(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }

    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < n {
        dp.push(0);
        j += 1;
    }

    dp[0] = grid[0][0];

    let mut j = 1;
    while j < n {
        dp[j] = dp[j - 1] + grid[0][j];
        j += 1;
    }

    let mut i = 1;
    while i < m {
        dp[0] = dp[0] + grid[i][0];

        let mut j = 1;
        while j < n {
            let from_up = dp[j];
            let from_left = dp[j - 1];

            let mut best = from_up;
            if from_left < best {
                best = from_left;
            }

            dp[j] = best + grid[i][j];
            j += 1;
        }

        i += 1;
    }

    dp[n - 1]
}
