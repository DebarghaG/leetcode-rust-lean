pub fn unique_paths_with_obstacles(obstacleGrid: &[Vec<i64>]) -> i64 {
    let m = obstacleGrid.len();
    if m == 0 {
        return 0;
    }

    let n = obstacleGrid[0].len();
    if n == 0 {
        return 0;
    }

    if obstacleGrid[0][0] == 1 {
        return 0;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < n {
        dp.push(0);
        j += 1;
    }

    dp[0] = 1;

    let mut i = 0;
    while i < m {
        let row = &obstacleGrid[i];
        let mut j = 0;
        while j < n {
            if row[j] == 1 {
                dp[j] = 0;
            } else if j > 0 {
                dp[j] = dp[j] + dp[j - 1];
            }
            j += 1;
        }
        i += 1;
    }

    dp[n - 1]
}
