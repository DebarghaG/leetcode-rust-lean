fn has_dir(t: i64, dir: i64) -> bool {
    if dir == 0 {
        // left
        t == 1 || t == 3 || t == 5
    } else if dir == 1 {
        // right
        t == 1 || t == 4 || t == 6
    } else if dir == 2 {
        // up
        t == 2 || t == 5 || t == 6
    } else {
        // down
        t == 2 || t == 3 || t == 4
    }
}

pub fn has_valid_path(grid: &[Vec<i64>]) -> bool {
    let m = grid.len();
    if m == 0 {
        return false;
    }

    let n = grid[0].len();
    if n == 0 {
        return false;
    }

    let total = m * n;
    let target = (m - 1) * n + (n - 1);

    let mut visited: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < total {
        visited.push(false);
        i += 1;
    }

    let mut queue: Vec<usize> = Vec::new();
    queue.push(0);
    visited[0] = true;

    let mut head: usize = 0;
    while head < queue.len() {
        let idx = queue[head];
        head += 1;

        if idx == target {
            return true;
        }

        let r = idx / n;
        let c = idx % n;
        let t = grid[r][c];

        // Move left: current cell must connect left, and left cell must connect right.
        if c > 0 && has_dir(t, 0) {
            let nt = grid[r][c - 1];
            if has_dir(nt, 1) {
                let nidx = r * n + (c - 1);
                if !visited[nidx] {
                    visited[nidx] = true;
                    queue.push(nidx);
                }
            }
        }

        // Move right: current cell must connect right, and right cell must connect left.
        if c + 1 < n && has_dir(t, 1) {
            let nt = grid[r][c + 1];
            if has_dir(nt, 0) {
                let nidx = r * n + (c + 1);
                if !visited[nidx] {
                    visited[nidx] = true;
                    queue.push(nidx);
                }
            }
        }

        // Move up: current cell must connect up, and upper cell must connect down.
        if r > 0 && has_dir(t, 2) {
            let nt = grid[r - 1][c];
            if has_dir(nt, 3) {
                let nidx = (r - 1) * n + c;
                if !visited[nidx] {
                    visited[nidx] = true;
                    queue.push(nidx);
                }
            }
        }

        // Move down: current cell must connect down, and lower cell must connect up.
        if r + 1 < m && has_dir(t, 3) {
            let nt = grid[r + 1][c];
            if has_dir(nt, 2) {
                let nidx = (r + 1) * n + c;
                if !visited[nidx] {
                    visited[nidx] = true;
                    queue.push(nidx);
                }
            }
        }
    }

    false
}
