fn feasible(dist: &[i64], n: usize, k: i64) -> bool {
    let total = n * n;
    let target = total - 1;

    if dist[0] < k {
        return false;
    }

    let mut visited: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < total {
        visited.push(false);
        i += 1;
    }

    let mut q: Vec<usize> = Vec::new();
    visited[0] = true;
    q.push(0);

    let mut head: usize = 0;
    while head < q.len() {
        let idx = q[head];
        head += 1;

        if idx == target {
            return true;
        }

        let r = idx / n;
        let c = idx % n;

        if r > 0 {
            let ni = idx - n;
            if !visited[ni] && dist[ni] >= k {
                visited[ni] = true;
                q.push(ni);
            }
        }
        if r + 1 < n {
            let ni = idx + n;
            if !visited[ni] && dist[ni] >= k {
                visited[ni] = true;
                q.push(ni);
            }
        }
        if c > 0 {
            let ni = idx - 1;
            if !visited[ni] && dist[ni] >= k {
                visited[ni] = true;
                q.push(ni);
            }
        }
        if c + 1 < n {
            let ni = idx + 1;
            if !visited[ni] && dist[ni] >= k {
                visited[ni] = true;
                q.push(ni);
            }
        }
    }

    false
}

pub fn maximum_safeness_factor(grid: &[Vec<i64>]) -> i64 {
    let n = grid.len();
    let total = n * n;

    let mut dist: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < total {
        dist.push(-1);
        i += 1;
    }

    let mut q: Vec<usize> = Vec::new();

    let mut r: usize = 0;
    while r < n {
        let mut c: usize = 0;
        while c < n {
            if grid[r][c] == 1 {
                let idx = r * n + c;
                dist[idx] = 0;
                q.push(idx);
            }
            c += 1;
        }
        r += 1;
    }

    let mut head: usize = 0;
    while head < q.len() {
        let idx = q[head];
        head += 1;

        let cr = idx / n;
        let cc = idx % n;
        let next_dist = dist[idx] + 1;

        if cr > 0 {
            let ni = idx - n;
            if dist[ni] < 0 {
                dist[ni] = next_dist;
                q.push(ni);
            }
        }
        if cr + 1 < n {
            let ni = idx + n;
            if dist[ni] < 0 {
                dist[ni] = next_dist;
                q.push(ni);
            }
        }
        if cc > 0 {
            let ni = idx - 1;
            if dist[ni] < 0 {
                dist[ni] = next_dist;
                q.push(ni);
            }
        }
        if cc + 1 < n {
            let ni = idx + 1;
            if dist[ni] < 0 {
                dist[ni] = next_dist;
                q.push(ni);
            }
        }
    }

    let mut hi: i64 = 0;
    i = 0;
    while i < total {
        if dist[i] > hi {
            hi = dist[i];
        }
        i += 1;
    }

    let mut lo: i64 = 0;
    while lo < hi {
        let mid = (lo + hi + 1) / 2;
        if feasible(&dist, n, mid) {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }

    lo
}
