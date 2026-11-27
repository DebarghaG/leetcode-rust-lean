pub fn closed_island(grid: &[Vec<i64>]) -> i64 {
    let n = grid.len();
    if n == 0 {
        return 0;
    }

    let m = grid[0].len();
    if m == 0 {
        return 0;
    }

    let mut g: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < m {
            row.push(grid[i][j]);
            j += 1;
        }
        g.push(row);
        i += 1;
    }

    let mut count: i64 = 0;
    let mut r0: usize = 0;

    while r0 < n {
        let mut c0: usize = 0;

        while c0 < m {
            if g[r0][c0] == 0 {
                let mut touches_boundary: bool = false;
                let mut stack_r: Vec<i64> = Vec::new();
                let mut stack_c: Vec<i64> = Vec::new();

                g[r0][c0] = 2;
                stack_r.push(r0 as i64);
                stack_c.push(c0 as i64);

                let mut head: usize = 0;

                while head < stack_r.len() {
                    let r = stack_r[head] as usize;
                    let c = stack_c[head] as usize;
                    head += 1;

                    if r == 0 || r == n - 1 || c == 0 || c == m - 1 {
                        touches_boundary = true;
                    }

                    if r > 0 {
                        let rr = r - 1;
                        if g[rr][c] == 0 {
                            g[rr][c] = 2;
                            stack_r.push(rr as i64);
                            stack_c.push(c as i64);
                        }
                    }

                    if r < n - 1 {
                        let rr = r + 1;
                        if g[rr][c] == 0 {
                            g[rr][c] = 2;
                            stack_r.push(rr as i64);
                            stack_c.push(c as i64);
                        }
                    }

                    if c > 0 {
                        let cc = c - 1;
                        if g[r][cc] == 0 {
                            g[r][cc] = 2;
                            stack_r.push(r as i64);
                            stack_c.push(cc as i64);
                        }
                    }

                    if c < m - 1 {
                        let cc = c + 1;
                        if g[r][cc] == 0 {
                            g[r][cc] = 2;
                            stack_r.push(r as i64);
                            stack_c.push(cc as i64);
                        }
                    }
                }

                if !touches_boundary {
                    count += 1;
                }
            }

            c0 += 1;
        }

        r0 += 1;
    }

    count
}
