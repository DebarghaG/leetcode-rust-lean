pub fn min_cost(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }
    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let total = m * n;
    let inf: i64 = 1000000000;

    // dist[v] = current best cost to reach cell v
    let mut dist: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < total {
        dist.push(inf);
        k = k + 1;
    }
    dist[0] = 0;

    // Bellman-Ford style relaxation with bounded scalar-driven loops only.
    let mut round: usize = 0;
    while round < total {
        let mut changed: bool = false;
        let mut i: usize = 0;
        while i < total {
            let u = i;
            let du = dist[u];
            if du < inf {
                let r = u / n;
                let c = u % n;
                let sign = grid[r][c];

                // move right
                if c + 1 < n {
                    let v = u + 1;
                    let mut w: i64 = 1;
                    if sign == 1 {
                        w = 0;
                    }
                    let nd = du + w;
                    if nd < dist[v] {
                        dist[v] = nd;
                        changed = true;
                    }
                }

                // move left
                if c > 0 {
                    let v = u - 1;
                    let mut w: i64 = 1;
                    if sign == 2 {
                        w = 0;
                    }
                    let nd = du + w;
                    if nd < dist[v] {
                        dist[v] = nd;
                        changed = true;
                    }
                }

                // move down
                if r + 1 < m {
                    let v = u + n;
                    let mut w: i64 = 1;
                    if sign == 3 {
                        w = 0;
                    }
                    let nd = du + w;
                    if nd < dist[v] {
                        dist[v] = nd;
                        changed = true;
                    }
                }

                // move up
                if r > 0 {
                    let v = u - n;
                    let mut w: i64 = 1;
                    if sign == 4 {
                        w = 0;
                    }
                    let nd = du + w;
                    if nd < dist[v] {
                        dist[v] = nd;
                        changed = true;
                    }
                }
            }
            i = i + 1;
        }

        round = round + 1;
        // Early convergence: force loop exit (no break / no boolean in condition).
        if !changed {
            round = total;
        }
    }

    dist[total - 1]
}
