pub fn maximum_minutes(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return -1;
    }
    let n = grid[0].len();
    if n == 0 {
        return -1;
    }

    let inf: i64 = 1000000000000000;

    let mut fire: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            row.push(inf);
            j += 1;
        }
        fire.push(row);
        i += 1;
    }

    let mut q: Vec<i64> = Vec::new();
    i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            if grid[i][j] == 1 {
                fire[i][j] = 0;
                q.push((i * n + j) as i64);
            }
            j += 1;
        }
        i += 1;
    }

    let mut head = 0;
    while head < q.len() {
        let idx = q[head] as usize;
        head += 1;
        let r = idx / n;
        let c = idx % n;
        let nt = fire[r][c] + 1;

        if r > 0 {
            let nr = r - 1;
            if grid[nr][c] != 2 && fire[nr][c] > nt {
                fire[nr][c] = nt;
                q.push((nr * n + c) as i64);
            }
        }
        if r + 1 < m {
            let nr = r + 1;
            if grid[nr][c] != 2 && fire[nr][c] > nt {
                fire[nr][c] = nt;
                q.push((nr * n + c) as i64);
            }
        }
        if c > 0 {
            let nc = c - 1;
            if grid[r][nc] != 2 && fire[r][nc] > nt {
                fire[r][nc] = nt;
                q.push((r * n + nc) as i64);
            }
        }
        if c + 1 < n {
            let nc = c + 1;
            if grid[r][nc] != 2 && fire[r][nc] > nt {
                fire[r][nc] = nt;
                q.push((r * n + nc) as i64);
            }
        }
    }

    if !can_reach(grid, &fire, 0) {
        return -1;
    }
    if can_reach(grid, &fire, 1000000000) {
        return 1000000000;
    }

    let mut lo: i64 = 0;
    let mut hi: i64 = 1000000000;
    while lo + 1 < hi {
        let mid = lo + (hi - lo) / 2;
        if can_reach(grid, &fire, mid) {
            lo = mid;
        } else {
            hi = mid;
        }
    }

    lo
}

fn can_reach(grid: &[Vec<i64>], fire: &[Vec<i64>], wait: i64) -> bool {
    let m = grid.len();
    if m == 0 {
        return false;
    }
    let n = grid[0].len();
    if n == 0 {
        return false;
    }

    let inf: i64 = 1000000000000000;

    if wait >= fire[0][0] {
        return false;
    }

    let mut person: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            row.push(inf);
            j += 1;
        }
        person.push(row);
        i += 1;
    }

    person[0][0] = wait;

    let mut q: Vec<i64> = Vec::new();
    q.push(0);

    let mut head = 0;
    let dm = m - 1;
    let dn = n - 1;
    let mut found = false;

    while head < q.len() && !found {
        let idx = q[head] as usize;
        head += 1;
        let r = idx / n;
        let c = idx % n;
        let nt = person[r][c] + 1;

        if r > 0 {
            let nr = r - 1;
            if grid[nr][c] == 0 && person[nr][c] == inf {
                if nr == dm && c == dn {
                    if nt <= fire[nr][c] {
                        found = true;
                    }
                } else if nt < fire[nr][c] {
                    person[nr][c] = nt;
                    q.push((nr * n + c) as i64);
                }
            }
        }

        if r + 1 < m {
            let nr = r + 1;
            if grid[nr][c] == 0 && person[nr][c] == inf {
                if nr == dm && c == dn {
                    if nt <= fire[nr][c] {
                        found = true;
                    }
                } else if nt < fire[nr][c] {
                    person[nr][c] = nt;
                    q.push((nr * n + c) as i64);
                }
            }
        }

        if c > 0 {
            let nc = c - 1;
            if grid[r][nc] == 0 && person[r][nc] == inf {
                if r == dm && nc == dn {
                    if nt <= fire[r][nc] {
                        found = true;
                    }
                } else if nt < fire[r][nc] {
                    person[r][nc] = nt;
                    q.push((r * n + nc) as i64);
                }
            }
        }

        if c + 1 < n {
            let nc = c + 1;
            if grid[r][nc] == 0 && person[r][nc] == inf {
                if r == dm && nc == dn {
                    if nt <= fire[r][nc] {
                        found = true;
                    }
                } else if nt < fire[r][nc] {
                    person[r][nc] = nt;
                    q.push((r * n + nc) as i64);
                }
            }
        }
    }

    found
}
