pub fn minimum_moves(grid: &[Vec<i64>]) -> i64 {
    let n = grid.len();
    if n == 0 {
        return -1;
    }

    let total = n * n * 2;
    let mut dist: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < total {
        dist.push(-1);
        i += 1;
    }

    let start_state = 0usize;
    let target_state = ((n - 1) * n + (n - 2)) * 2;

    let mut q: Vec<usize> = Vec::new();
    q.push(start_state);
    dist[start_state] = 0;

    let mut head = 0usize;
    while head < q.len() {
        let state = q[head];
        head += 1;

        let d = dist[state];
        if state == target_state {
            return d;
        }

        let ori = state % 2;
        let pos = state / 2;
        let r = pos / n;
        let c = pos % n;

        if ori == 0 {
            // Horizontal snake occupying (r, c) and (r, c + 1).

            // Move right.
            if c + 2 < n {
                if grid[r][c + 2] == 0 {
                    let ns = (r * n + (c + 1)) * 2;
                    if dist[ns] == -1 {
                        dist[ns] = d + 1;
                        q.push(ns);
                    }
                }
            }

            // Move down.
            if r + 1 < n {
                if grid[r + 1][c] == 0 && grid[r + 1][c + 1] == 0 {
                    let ns = ((r + 1) * n + c) * 2;
                    if dist[ns] == -1 {
                        dist[ns] = d + 1;
                        q.push(ns);
                    }
                }
            }

            // Rotate clockwise to vertical.
            if r + 1 < n {
                if grid[r + 1][c] == 0 && grid[r + 1][c + 1] == 0 {
                    let ns = (r * n + c) * 2 + 1;
                    if dist[ns] == -1 {
                        dist[ns] = d + 1;
                        q.push(ns);
                    }
                }
            }
        } else {
            // Vertical snake occupying (r, c) and (r + 1, c).

            // Move right.
            if c + 1 < n {
                if grid[r][c + 1] == 0 && grid[r + 1][c + 1] == 0 {
                    let ns = (r * n + (c + 1)) * 2 + 1;
                    if dist[ns] == -1 {
                        dist[ns] = d + 1;
                        q.push(ns);
                    }
                }
            }

            // Move down.
            if r + 2 < n {
                if grid[r + 2][c] == 0 {
                    let ns = ((r + 1) * n + c) * 2 + 1;
                    if dist[ns] == -1 {
                        dist[ns] = d + 1;
                        q.push(ns);
                    }
                }
            }

            // Rotate counterclockwise to horizontal.
            if c + 1 < n {
                if grid[r][c + 1] == 0 && grid[r + 1][c + 1] == 0 {
                    let ns = (r * n + c) * 2;
                    if dist[ns] == -1 {
                        dist[ns] = d + 1;
                        q.push(ns);
                    }
                }
            }
        }
    }

    -1
}
