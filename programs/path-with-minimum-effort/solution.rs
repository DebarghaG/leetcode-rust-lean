pub fn minimum_effort_path(heights: &[Vec<i64>]) -> i64 {
    let rows = heights.len();
    if rows == 0 {
        return 0;
    }
    let cols = heights[0].len();
    if cols == 0 {
        return 0;
    }
    if rows == 1 && cols == 1 {
        return 0;
    }

    let mut lo: i64 = 0;
    let mut hi: i64 = 1_000_000;

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if can_reach(heights, mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo
}

fn can_reach(heights: &[Vec<i64>], threshold: i64) -> bool {
    let rows = heights.len();
    let cols = heights[0].len();
    let n = rows * cols;

    let mut visited: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < n {
        visited.push(false);
        i += 1;
    }

    let mut queue: Vec<usize> = Vec::new();
    queue.push(0);
    visited[0] = true;

    let mut head = 0;
    while head < queue.len() {
        let u = queue[head];
        head += 1;

        if u == n - 1 {
            return true;
        }

        let r = u / cols;
        let c = u % cols;
        let h = heights[r][c];

        if r > 0 {
            let v = u - cols;
            if !visited[v] {
                let mut diff = h - heights[r - 1][c];
                if diff < 0 {
                    diff = -diff;
                }
                if diff <= threshold {
                    visited[v] = true;
                    queue.push(v);
                }
            }
        }

        if r + 1 < rows {
            let v = u + cols;
            if !visited[v] {
                let mut diff = h - heights[r + 1][c];
                if diff < 0 {
                    diff = -diff;
                }
                if diff <= threshold {
                    visited[v] = true;
                    queue.push(v);
                }
            }
        }

        if c > 0 {
            let v = u - 1;
            if !visited[v] {
                let mut diff = h - heights[r][c - 1];
                if diff < 0 {
                    diff = -diff;
                }
                if diff <= threshold {
                    visited[v] = true;
                    queue.push(v);
                }
            }
        }

        if c + 1 < cols {
            let v = u + 1;
            if !visited[v] {
                let mut diff = h - heights[r][c + 1];
                if diff < 0 {
                    diff = -diff;
                }
                if diff <= threshold {
                    visited[v] = true;
                    queue.push(v);
                }
            }
        }
    }

    false
}
