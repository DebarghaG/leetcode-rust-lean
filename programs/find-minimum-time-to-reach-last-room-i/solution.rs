pub fn min_time_to_reach(moveTime: &[Vec<i64>]) -> i64 {
    let n = moveTime.len();
    if n == 0 {
        return 0;
    }

    let m = moveTime[0].len();
    if m == 0 {
        return 0;
    }

    let total = n * m;
    if total == 0 {
        return 0;
    }

    let target = total - 1;
    let inf: i64 = 4000000000000000000;

    let mut dist: Vec<i64> = Vec::new();
    let mut visited: Vec<bool> = Vec::new();

    let mut i: usize = 0;
    while i < total {
        dist.push(inf);
        visited.push(false);
        i = i + 1;
    }

    dist[0] = 0;

    let mut done: usize = 0;
    while done < total {
        let mut u: usize = total;
        let mut best: i64 = inf;
        let mut idx: usize = 0;

        while idx < total {
            if !visited[idx] && dist[idx] < best {
                best = dist[idx];
                u = idx;
            }
            idx = idx + 1;
        }

        if u == total {
            break;
        }

        if u == target {
            return dist[u];
        }

        visited[u] = true;

        let r: usize = u / m;
        let c: usize = u % m;

        if r > 0 {
            let v = u - m;
            if !visited[v] {
                let mt = moveTime[r - 1][c];
                let base = if dist[u] > mt { dist[u] } else { mt };
                let nd = base + 1;
                if nd < dist[v] {
                    dist[v] = nd;
                }
            }
        }

        if r + 1 < n {
            let v = u + m;
            if !visited[v] {
                let mt = moveTime[r + 1][c];
                let base = if dist[u] > mt { dist[u] } else { mt };
                let nd = base + 1;
                if nd < dist[v] {
                    dist[v] = nd;
                }
            }
        }

        if c > 0 {
            let v = u - 1;
            if !visited[v] {
                let mt = moveTime[r][c - 1];
                let base = if dist[u] > mt { dist[u] } else { mt };
                let nd = base + 1;
                if nd < dist[v] {
                    dist[v] = nd;
                }
            }
        }

        if c + 1 < m {
            let v = u + 1;
            if !visited[v] {
                let mt = moveTime[r][c + 1];
                let base = if dist[u] > mt { dist[u] } else { mt };
                let nd = base + 1;
                if nd < dist[v] {
                    dist[v] = nd;
                }
            }
        }

        done = done + 1;
    }

    dist[target]
}
