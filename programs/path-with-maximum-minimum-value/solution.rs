pub fn maximum_minimum_path(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }
    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let mut lo: i64 = 0;
    let mut hi: i64 = 1_000_000_000;

    while lo < hi {
        let mid: i64 = lo + (hi - lo + 1) / 2;
        if can_connect(grid, mid) {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }

    lo
}

fn can_connect(grid: &[Vec<i64>], threshold: i64) -> bool {
    let m = grid.len();
    let n = grid[0].len();

    if grid[0][0] < threshold {
        return false;
    }

    let total = m * n;
    let target = total - 1;

    let mut visited: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < total {
        visited.push(0);
        i += 1;
    }

    let mut queue: Vec<usize> = Vec::new();
    queue.push(0);
    visited[0] = 1;

    let mut head: usize = 0;
    while head < queue.len() {
        let idx = queue[head];
        head += 1;

        if idx == target {
            return true;
        }

        let r = idx / n;
        let c = idx % n;

        if r > 0 {
            let nr = r - 1;
            let ni = nr * n + c;
            if visited[ni] == 0 && grid[nr][c] >= threshold {
                visited[ni] = 1;
                queue.push(ni);
            }
        }

        if r + 1 < m {
            let nr = r + 1;
            let ni = nr * n + c;
            if visited[ni] == 0 && grid[nr][c] >= threshold {
                visited[ni] = 1;
                queue.push(ni);
            }
        }

        if c > 0 {
            let nc = c - 1;
            let ni = r * n + nc;
            if visited[ni] == 0 && grid[r][nc] >= threshold {
                visited[ni] = 1;
                queue.push(ni);
            }
        }

        if c + 1 < n {
            let nc = c + 1;
            let ni = r * n + nc;
            if visited[ni] == 0 && grid[r][nc] >= threshold {
                visited[ni] = 1;
                queue.push(ni);
            }
        }
    }

    false
}
