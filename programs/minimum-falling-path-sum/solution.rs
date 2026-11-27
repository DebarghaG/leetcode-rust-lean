pub fn min_falling_path_sum(matrix: &[Vec<i64>]) -> i64 {
    let n = matrix.len();
    if n == 0 {
        return 0;
    }

    let m = matrix[0].len();

    // The problem specifies an n x n matrix. For malformed rectangular
    // inputs, the expected convention here is to return 0.
    if n != m {
        return 0;
    }

    let mut r = 0;
    while r < n {
        if matrix[r].len() != m {
            return 0;
        }
        r += 1;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < m {
        dp.push(matrix[0][j]);
        j += 1;
    }

    let mut row = 1;
    while row < n {
        let mut next: Vec<i64> = Vec::new();
        let mut col = 0;

        while col < m {
            let mut best = dp[col];

            if col > 0 {
                if dp[col - 1] < best {
                    best = dp[col - 1];
                }
            }

            if col + 1 < m {
                if dp[col + 1] < best {
                    best = dp[col + 1];
                }
            }

            next.push(matrix[row][col] + best);
            col += 1;
        }

        dp = next;
        row += 1;
    }

    let mut ans = dp[0];
    let mut k = 1;
    while k < m {
        if dp[k] < ans {
            ans = dp[k];
        }
        k += 1;
    }

    ans
}
