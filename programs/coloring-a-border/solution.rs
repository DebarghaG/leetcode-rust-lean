pub fn color_border(grid: &[Vec<i64>], row: i64, col: i64, color: i64) -> Vec<Vec<i64>> {
    let m = grid.len();
    let n = grid[0].len();

    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < m {
        let mut new_row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            new_row.push(grid[i][j]);
            j += 1;
        }
        out.push(new_row);
        i += 1;
    }

    let start_r = row as usize;
    let start_c = col as usize;
    let old_color = grid[start_r][start_c];

    if old_color == color {
        return out;
    }

    let total = m * n;
    let mut visited: Vec<bool> = Vec::new();
    let mut k = 0;
    while k < total {
        visited.push(false);
        k += 1;
    }

    let mut queue: Vec<usize> = Vec::new();
    let start_idx = start_r * n + start_c;
    visited[start_idx] = true;
    queue.push(start_idx);

    let mut head = 0;
    while head < queue.len() {
        let idx = queue[head];
        head += 1;

        let r = idx / n;
        let c = idx % n;

        let mut is_border = false;

        if r == 0 || r + 1 == m || c == 0 || c + 1 == n {
            is_border = true;
        }

        if r > 0 {
            let nr = r - 1;
            if grid[nr][c] != old_color {
                is_border = true;
            } else {
                let nidx = nr * n + c;
                if !visited[nidx] {
                    visited[nidx] = true;
                    queue.push(nidx);
                }
            }
        }

        if r + 1 < m {
            let nr = r + 1;
            if grid[nr][c] != old_color {
                is_border = true;
            } else {
                let nidx = nr * n + c;
                if !visited[nidx] {
                    visited[nidx] = true;
                    queue.push(nidx);
                }
            }
        }

        if c > 0 {
            let nc = c - 1;
            if grid[r][nc] != old_color {
                is_border = true;
            } else {
                let nidx = r * n + nc;
                if !visited[nidx] {
                    visited[nidx] = true;
                    queue.push(nidx);
                }
            }
        }

        if c + 1 < n {
            let nc = c + 1;
            if grid[r][nc] != old_color {
                is_border = true;
            } else {
                let nidx = r * n + nc;
                if !visited[nidx] {
                    visited[nidx] = true;
                    queue.push(nidx);
                }
            }
        }

        if is_border {
            out[r][c] = color;
        }
    }

    out
}
