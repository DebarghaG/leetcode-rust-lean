pub fn count_paths(n: i64, roads: &[Vec<i64>]) -> i64 {
    let mod_val: i64 = 1000000007;
    let inf: i64 = 1000000000000000000;
    let n_usize = n as usize;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n_usize {
            row.push(0);
            j += 1;
        }
        adj.push(row);
        i += 1;
    }

    let mut r: usize = 0;
    while r < roads.len() {
        let u = roads[r][0] as usize;
        let v = roads[r][1] as usize;
        let w = roads[r][2];
        adj[u][v] = w;
        adj[v][u] = w;
        r += 1;
    }

    let mut dist: Vec<i64> = Vec::new();
    let mut ways: Vec<i64> = Vec::new();
    let mut visited: Vec<bool> = Vec::new();

    i = 0;
    while i < n_usize {
        dist.push(inf);
        ways.push(0);
        visited.push(false);
        i += 1;
    }

    dist[0] = 0;
    ways[0] = 1;

    let mut step: usize = 0;
    while step < n_usize {
        let mut u: usize = n_usize;
        let mut best: i64 = inf;

        let mut a: usize = 0;
        while a < n_usize {
            if !visited[a] && dist[a] < best {
                best = dist[a];
                u = a;
            }
            a += 1;
        }

        if u == n_usize {
            break;
        }

        visited[u] = true;

        let mut v: usize = 0;
        while v < n_usize {
            let w = adj[u][v];
            if w > 0 && !visited[v] {
                let nd = dist[u] + w;
                if nd < dist[v] {
                    dist[v] = nd;
                    ways[v] = ways[u];
                } else if nd == dist[v] {
                    ways[v] = (ways[v] + ways[u]) % mod_val;
                }
            }
            v += 1;
        }

        step += 1;
    }

    ways[n_usize - 1]
}
