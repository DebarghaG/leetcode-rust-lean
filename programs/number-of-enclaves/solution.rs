pub fn num_enclaves(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }
    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let mut seen: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            row.push(0);
            j += 1;
        }
        seen.push(row);
        i += 1;
    }

    let n_i = n as i64;
    let mut stack: Vec<i64> = Vec::new();

    let mut j = 0;
    while j < n {
        if grid[0][j] == 1 && seen[0][j] == 0 {
            seen[0][j] = 1;
            stack.push(j as i64);
        }
        if m > 1 && grid[m - 1][j] == 1 && seen[m - 1][j] == 0 {
            seen[m - 1][j] = 1;
            stack.push(((m - 1) as i64) * n_i + (j as i64));
        }
        j += 1;
    }

    let mut i = 0;
    while i < m {
        if grid[i][0] == 1 && seen[i][0] == 0 {
            seen[i][0] = 1;
            stack.push((i as i64) * n_i);
        }
        if n > 1 && grid[i][n - 1] == 1 && seen[i][n - 1] == 0 {
            seen[i][n - 1] = 1;
            stack.push((i as i64) * n_i + ((n - 1) as i64));
        }
        i += 1;
    }

    let mut head: usize = 0;
    while head < stack.len() {
        let pos = stack[head];
        head += 1;

        let r_i = pos / n_i;
        let c_i = pos % n_i;
        let r = r_i as usize;
        let c = c_i as usize;

        if r > 0 {
            if grid[r - 1][c] == 1 && seen[r - 1][c] == 0 {
                seen[r - 1][c] = 1;
                stack.push(((r - 1) as i64) * n_i + (c as i64));
            }
        }

        if r + 1 < m {
            if grid[r + 1][c] == 1 && seen[r + 1][c] == 0 {
                seen[r + 1][c] = 1;
                stack.push(((r + 1) as i64) * n_i + (c as i64));
            }
        }

        if c > 0 {
            if grid[r][c - 1] == 1 && seen[r][c - 1] == 0 {
                seen[r][c - 1] = 1;
                stack.push((r as i64) * n_i + ((c - 1) as i64));
            }
        }

        if c + 1 < n {
            if grid[r][c + 1] == 1 && seen[r][c + 1] == 0 {
                seen[r][c + 1] = 1;
                stack.push((r as i64) * n_i + ((c + 1) as i64));
            }
        }
    }

    let mut ans: i64 = 0;
    let mut i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            if grid[i][j] == 1 && seen[i][j] == 0 {
                ans += 1;
            }
            j += 1;
        }
        i += 1;
    }

    ans
}
