pub fn count_squares(matrix: &[Vec<i64>]) -> i64 {
    let m = matrix.len();
    if m == 0 {
        return 0;
    }

    let n = matrix[0].len();
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
    i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            if matrix[i][j] == 1 {
                let mut value: i64 = 1;

                if i > 0 && j > 0 {
                    let mut smallest = dp[i - 1][j];
                    if dp[i][j - 1] < smallest {
                        smallest = dp[i][j - 1];
                    }
                    if dp[i - 1][j - 1] < smallest {
                        smallest = dp[i - 1][j - 1];
                    }
                    value = smallest + 1;
                }

                dp[i][j] = value;
                total += value;
            }
            j += 1;
        }
        i += 1;
    }

    total
}
