pub fn find_max_fish(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }

    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let mut g: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            row.push(grid[i][j]);
            j += 1;
        }
        g.push(row);
        i += 1;
    }

    let mut best: i64 = 0;
    let mut r: usize = 0;
    while r < m {
        let mut c: usize = 0;
        while c < n {
            if g[r][c] > 0 {
                let mut total: i64 = 0;
                let mut stack: Vec<i64> = Vec::new();

                total = total + g[r][c];
                g[r][c] = 0;
                stack.push((r * n + c) as i64);

                let mut sp: usize = 0;
                while sp < stack.len() {
                    let idx_i64 = stack[sp];
                    let idx = idx_i64 as usize;
                    sp += 1;

                    let rr = idx / n;
                    let cc = idx % n;

                    if rr > 0 {
                        let nr = rr - 1;
                        if g[nr][cc] > 0 {
                            total = total + g[nr][cc];
                            g[nr][cc] = 0;
                            stack.push((nr * n + cc) as i64);
                        }
                    }

                    if rr + 1 < m {
                        let nr = rr + 1;
                        if g[nr][cc] > 0 {
                            total = total + g[nr][cc];
                            g[nr][cc] = 0;
                            stack.push((nr * n + cc) as i64);
                        }
                    }

                    if cc > 0 {
                        let nc = cc - 1;
                        if g[rr][nc] > 0 {
                            total = total + g[rr][nc];
                            g[rr][nc] = 0;
                            stack.push((rr * n + nc) as i64);
                        }
                    }

                    if cc + 1 < n {
                        let nc = cc + 1;
                        if g[rr][nc] > 0 {
                            total = total + g[rr][nc];
                            g[rr][nc] = 0;
                            stack.push((rr * n + nc) as i64);
                        }
                    }
                }

                if total > best {
                    best = total;
                }
            }
            c += 1;
        }
        r += 1;
    }

    best
}
