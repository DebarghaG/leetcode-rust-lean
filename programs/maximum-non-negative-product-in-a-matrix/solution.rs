pub fn max_product_path(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    let n = grid[0].len();

    let mut max_dp: Vec<Vec<i64>> = Vec::new();
    let mut min_dp: Vec<Vec<i64>> = Vec::new();

    let mut i = 0;
    while i < m {
        let mut row_max: Vec<i64> = Vec::new();
        let mut row_min: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            row_max.push(0);
            row_min.push(0);
            j += 1;
        }
        max_dp.push(row_max);
        min_dp.push(row_min);
        i += 1;
    }

    i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            let v = grid[i][j];

            if i == 0 && j == 0 {
                max_dp[i][j] = v;
                min_dp[i][j] = v;
            } else {
                let mut has_value = false;
                let mut best_max = 0;
                let mut best_min = 0;

                if i > 0 {
                    let a = max_dp[i - 1][j] * v;
                    let b = min_dp[i - 1][j] * v;

                    if !has_value {
                        best_max = a;
                        best_min = a;
                        has_value = true;
                    } else {
                        if a > best_max {
                            best_max = a;
                        }
                        if a < best_min {
                            best_min = a;
                        }
                    }

                    if b > best_max {
                        best_max = b;
                    }
                    if b < best_min {
                        best_min = b;
                    }
                }

                if j > 0 {
                    let a = max_dp[i][j - 1] * v;
                    let b = min_dp[i][j - 1] * v;

                    if !has_value {
                        best_max = a;
                        best_min = a;
                        has_value = true;
                    } else {
                        if a > best_max {
                            best_max = a;
                        }
                        if a < best_min {
                            best_min = a;
                        }
                    }

                    if b > best_max {
                        best_max = b;
                    }
                    if b < best_min {
                        best_min = b;
                    }
                }

                max_dp[i][j] = best_max;
                min_dp[i][j] = best_min;
            }

            j += 1;
        }
        i += 1;
    }

    let max_product = max_dp[m - 1][n - 1];

    if max_product < 0 {
        -1
    } else {
        max_product % 1_000_000_007
    }
}
