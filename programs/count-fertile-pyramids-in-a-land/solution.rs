pub fn count_pyramids(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }
    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let mut dp: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            row.push(0);
            j += 1;
        }
        dp.push(row);
        i += 1;
    }

    let mut total: i64 = 0;

    // Count ordinary pyramids: apex above, expanding downwards.
    i = m;
    while i > 0 {
        i -= 1;
        let mut j = 0;
        while j < n {
            if grid[i][j] == 1 {
                if i + 1 < m {
                    let left = if j > 0 { dp[i + 1][j - 1] } else { 0 };
                    let mid = dp[i + 1][j];
                    let right = if j + 1 < n { dp[i + 1][j + 1] } else { 0 };

                    let mut mn = left;
                    if mid < mn {
                        mn = mid;
                    }
                    if right < mn {
                        mn = right;
                    }

                    dp[i][j] = mn + 1;
                } else {
                    dp[i][j] = 1;
                }

                total += dp[i][j] - 1;
            } else {
                dp[i][j] = 0;
            }
            j += 1;
        }
    }

    // Reset dp for inverse pyramids.
    i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            dp[i][j] = 0;
            j += 1;
        }
        i += 1;
    }

    // Count inverse pyramids: apex below, expanding upwards.
    i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            if grid[i][j] == 1 {
                if i > 0 {
                    let left = if j > 0 { dp[i - 1][j - 1] } else { 0 };
                    let mid = dp[i - 1][j];
                    let right = if j + 1 < n { dp[i - 1][j + 1] } else { 0 };

                    let mut mn = left;
                    if mid < mn {
                        mn = mid;
                    }
                    if right < mn {
                        mn = right;
                    }

                    dp[i][j] = mn + 1;
                } else {
                    dp[i][j] = 1;
                }

                total += dp[i][j] - 1;
            } else {
                dp[i][j] = 0;
            }
            j += 1;
        }
        i += 1;
    }

    total
}
