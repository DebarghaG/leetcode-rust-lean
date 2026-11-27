pub fn is_there_a_path(grid: &[Vec<i64>]) -> bool {
    let m = grid.len();
    let n = grid[0].len();

    // We track (#1 - #0) along a path. Its absolute value is at most m + n - 1.
    let offset = m + n;
    let width = offset * 2 + 1;
    let total = m * n * width;

    let mut dp: Vec<bool> = Vec::new();
    let mut i = 0usize;
    while i < total {
        dp.push(false);
        i += 1;
    }

    // k = (#1 - #0) + offset.
    // Starting cell contributes +1 to the difference if it is a 1, else -1.
    let start_k = if grid[0][0] == 1 { offset + 1 } else { offset - 1 };
    dp[start_k] = true;

    let mut r = 0usize;
    while r < m {
        let mut c = 0usize;
        while c < n {
            let base = (r * n + c) * width;

            let mut k = 0usize;
            while k < width {
                if dp[base + k] {
                    if c + 1 < n {
                        let next_base = (r * n + (c + 1)) * width;
                        let next_k = if grid[r][c + 1] == 1 { k + 1 } else { k - 1 };
                        dp[next_base + next_k] = true;
                    }

                    if r + 1 < m {
                        let next_base = ((r + 1) * n + c) * width;
                        let next_k = if grid[r + 1][c] == 1 { k + 1 } else { k - 1 };
                        dp[next_base + next_k] = true;
                    }
                }

                k += 1;
            }

            c += 1;
        }

        r += 1;
    }

    let end_base = ((m - 1) * n + (n - 1)) * width;
    dp[end_base + offset]
}
