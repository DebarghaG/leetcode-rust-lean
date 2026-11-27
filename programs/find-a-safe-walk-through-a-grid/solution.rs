pub fn find_safe_walk(grid: &[Vec<i64>], health: i64) -> bool {
    let m = grid.len();
    if m == 0 {
        return false;
    }

    let n = grid[0].len();
    if n == 0 {
        return false;
    }

    let total = m * n;
    let inf: i64 = 1_000_000_000;

    let mut dist: Vec<i64> = Vec::new();
    let mut visited: Vec<bool> = Vec::new();

    let mut k = 0;
    while k < total {
        dist.push(inf);
        visited.push(false);
        k += 1;
    }

    dist[0] = grid[0][0];

    let mut count = 0;
    while count < total {
        let mut u: usize = total;
        let mut best: i64 = inf;

        let mut idx = 0;
        while idx < total {
            if !visited[idx] && dist[idx] < best {
                best = dist[idx];
                u = idx;
            }
            idx += 1;
        }

        if u == total {
            break;
        }

        visited[u] = true;

        if u == total - 1 {
            break;
        }

        let ui = u / n;
        let uj = u % n;

        if ui > 0 {
            let v = (ui - 1) * n + uj;
            let w = grid[ui - 1][uj];
            if !visited[v] && best + w < dist[v] {
                dist[v] = best + w;
            }
        }

        if ui + 1 < m {
            let v = (ui + 1) * n + uj;
            let w = grid[ui + 1][uj];
            if !visited[v] && best + w < dist[v] {
                dist[v] = best + w;
            }
        }

        if uj > 0 {
            let v = ui * n + (uj - 1);
            let w = grid[ui][uj - 1];
            if !visited[v] && best + w < dist[v] {
                dist[v] = best + w;
            }
        }

        if uj + 1 < n {
            let v = ui * n + (uj + 1);
            let w = grid[ui][uj + 1];
            if !visited[v] && best + w < dist[v] {
                dist[v] = best + w;
            }
        }

        count += 1;
    }

    dist[total - 1] < health
}
