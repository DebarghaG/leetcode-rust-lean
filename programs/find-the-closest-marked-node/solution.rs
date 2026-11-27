pub fn minimum_distance(n: i64, edges: &[Vec<i64>], s: i64, marked: &[i64]) -> i64 {
    let n_usize = n as usize;
    let inf: i64 = 1_000_000_000_000_000_000;

    let mut dist: Vec<i64> = Vec::new();
    let mut visited: Vec<bool> = Vec::new();

    let mut i = 0usize;
    while i < n_usize {
        dist.push(inf);
        visited.push(false);
        i += 1;
    }

    dist[s as usize] = 0;

    let mut step = 0usize;
    while step < n_usize {
        let mut u: i64 = -1;
        let mut best: i64 = inf;

        let mut j = 0usize;
        while j < n_usize {
            if !visited[j] && dist[j] < best {
                best = dist[j];
                u = j as i64;
            }
            j += 1;
        }

        if u == -1 {
            break;
        }

        let uu = u as usize;

        let mut is_marked = false;
        let mut mi = 0usize;
        while mi < marked.len() {
            if marked[mi] == u {
                is_marked = true;
            }
            mi += 1;
        }

        if is_marked {
            return best;
        }

        visited[uu] = true;

        let mut ei = 0usize;
        while ei < edges.len() {
            let e = &edges[ei];
            if e[0] == u {
                let v = e[1] as usize;
                if !visited[v] {
                    let new_dist = dist[uu] + e[2];
                    if new_dist < dist[v] {
                        dist[v] = new_dist;
                    }
                }
            }
            ei += 1;
        }

        step += 1;
    }

    -1
}
