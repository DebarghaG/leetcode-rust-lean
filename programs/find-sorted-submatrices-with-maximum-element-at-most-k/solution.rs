pub fn count_submatrices(grid: &[Vec<i64>], k: i64) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }
    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    // g[r][c] = maximum length of a valid suffix ending at column c in row r:
    // all values <= k and non-increasing.
    let mut g: Vec<Vec<i64>> = Vec::new();
    let mut r = 0;
    while r < m {
        let mut row_g: Vec<i64> = Vec::new();
        let mut c = 0;
        while c < n {
            let value = grid[r][c];
            if value > k {
                row_g.push(0);
            } else if c == 0 {
                row_g.push(1);
            } else {
                let prev_value = grid[r][c - 1];
                let prev_len = row_g[c - 1];
                if prev_value >= value && prev_len > 0 {
                    row_g.push(prev_len + 1);
                } else {
                    row_g.push(1);
                }
            }
            c += 1;
        }
        g.push(row_g);
        r += 1;
    }

    let mut total: i64 = 0;
    let mut c = 0;
    while c < n {
        let mut dp: i64 = 0;
        let mut stack_vals: Vec<i64> = Vec::new();
        let mut stack_counts: Vec<i64> = Vec::new();

        let mut r2 = 0;
        while r2 < m {
            let x = g[r2][c];

            if x == 0 {
                dp = 0;
                stack_vals.clear();
                stack_counts.clear();
            } else {
                let mut count: i64 = 1;
                let mut stop = false;

                while !stop {
                    let slen = stack_vals.len();
                    if slen == 0 {
                        stop = true;
                    } else {
                        let top_val = stack_vals[slen - 1];
                        if top_val >= x {
                            let top_count = stack_counts[slen - 1];
                            stack_vals.pop();
                            stack_counts.pop();

                            count += top_count;
                            dp -= top_val * top_count;
                        } else {
                            stop = true;
                        }
                    }
                }

                dp += x * count;
                total += dp;

                stack_vals.push(x);
                stack_counts.push(count);
            }

            r2 += 1;
        }

        c += 1;
    }

    total
}
