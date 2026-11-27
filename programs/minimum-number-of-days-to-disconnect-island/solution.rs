pub fn min_days(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }
    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    if !connected(grid, -1, -1) {
        return 0;
    }

    let mut ans: i64 = 2;
    let mut i = 0usize;
    while i < m && ans == 2 {
        let mut j = 0usize;
        while j < n && ans == 2 {
            if grid[i][j] == 1 {
                if !connected(grid, i as i64, j as i64) {
                    ans = 1;
                }
            }
            j += 1;
        }
        i += 1;
    }

    ans
}

fn connected(grid: &[Vec<i64>], ri: i64, rj: i64) -> bool {
    let m = grid.len();
    if m == 0 {
        return false;
    }
    let n = grid[0].len();
    if n == 0 {
        return false;
    }

    let mut total_land: i64 = 0;
    let mut sr: i64 = -1;
    let mut sc: i64 = -1;

    let mut i = 0usize;
    while i < m {
        let mut j = 0usize;
        while j < n {
            if grid[i][j] == 1 {
                let removed = ri >= 0 && (i as i64) == ri && (j as i64) == rj;
                if !removed {
                    total_land += 1;
                    if sr < 0 {
                        sr = i as i64;
                        sc = j as i64;
                    }
                }
            }
            j += 1;
        }
        i += 1;
    }

    if total_land == 0 {
        return false;
    }

    let cells = m * n;
    let mut visited: Vec<bool> = Vec::new();
    let mut k = 0usize;
    while k < cells {
        visited.push(false);
        k += 1;
    }

    let start = (sr as usize) * n + (sc as usize);
    visited[start] = true;

    let mut queue: Vec<i64> = Vec::new();
    queue.push(start as i64);
    let mut head: usize = 0;
    let mut count: i64 = 0;

    while head < queue.len() {
        let cur = queue[head];
        head += 1;
        count += 1;

        let ci = (cur / (n as i64)) as usize;
        let cj = (cur % (n as i64)) as usize;

        if ci > 0 {
            let ni = ci - 1;
            let nj = cj;
            let removed_n = ri >= 0 && (ni as i64) == ri && (nj as i64) == rj;
            if grid[ni][nj] == 1 && !removed_n {
                let nidx = ni * n + nj;
                if !visited[nidx] {
                    visited[nidx] = true;
                    queue.push(nidx as i64);
                }
            }
        }

        if ci + 1 < m {
            let ni = ci + 1;
            let nj = cj;
            let removed_n = ri >= 0 && (ni as i64) == ri && (nj as i64) == rj;
            if grid[ni][nj] == 1 && !removed_n {
                let nidx = ni * n + nj;
                if !visited[nidx] {
                    visited[nidx] = true;
                    queue.push(nidx as i64);
                }
            }
        }

        if cj > 0 {
            let ni = ci;
            let nj = cj - 1;
            let removed_n = ri >= 0 && (ni as i64) == ri && (nj as i64) == rj;
            if grid[ni][nj] == 1 && !removed_n {
                let nidx = ni * n + nj;
                if !visited[nidx] {
                    visited[nidx] = true;
                    queue.push(nidx as i64);
                }
            }
        }

        if cj + 1 < n {
            let ni = ci;
            let nj = cj + 1;
            let removed_n = ri >= 0 && (ni as i64) == ri && (nj as i64) == rj;
            if grid[ni][nj] == 1 && !removed_n {
                let nidx = ni * n + nj;
                if !visited[nidx] {
                    visited[nidx] = true;
                    queue.push(nidx as i64);
                }
            }
        }
    }

    count == total_land
}
