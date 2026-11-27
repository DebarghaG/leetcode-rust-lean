pub fn reachable_nodes(edges: &[Vec<i64>], maxMoves: i64, n: i64) -> i64 {
    if n <= 0 {
        return 0;
    }

    let n_usize = n as usize;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        adj.push(Vec::new());
        i += 1;
    }

    let m = edges.len();
    let mut e: usize = 0;
    while e < m {
        let u_i64 = edges[e][0];
        let v_i64 = edges[e][1];
        let c = edges[e][2];
        let u = u_i64 as usize;
        let v = v_i64 as usize;
        let w = c + 1;

        adj[u].push(v_i64);
        adj[u].push(w);
        adj[v].push(u_i64);
        adj[v].push(w);

        e += 1;
    }

    let inf: i64 = 1000000000000000000;
    let mut dist: Vec<i64> = Vec::new();
    let mut used: Vec<bool> = Vec::new();

    i = 0;
    while i < n_usize {
        dist.push(inf);
        used.push(false);
        i += 1;
    }

    dist[0] = 0;

    let mut iter: usize = 0;
    while iter < n_usize {
        let mut u: usize = n_usize;
        let mut best: i64 = inf;

        let mut j: usize = 0;
        while j < n_usize {
            if !used[j] && dist[j] < best {
                best = dist[j];
                u = j;
            }
            j += 1;
        }

        if u == n_usize {
            break;
        }
        if best > maxMoves {
            break;
        }

        used[u] = true;

        let row = &adj[u];
        let deg = row.len() / 2;
        let mut k: usize = 0;
        while k < deg {
            let v = row[2 * k] as usize;
            let w = row[2 * k + 1];

            if !used[v] {
                let nd = dist[u] + w;
                if nd < dist[v] {
                    dist[v] = nd;
                }
            }

            k += 1;
        }

        iter += 1;
    }

    let mut ans: i64 = 0;

    i = 0;
    while i < n_usize {
        if dist[i] <= maxMoves {
            ans += 1;
        }
        i += 1;
    }

    e = 0;
    while e < m {
        let u = edges[e][0] as usize;
        let v = edges[e][1] as usize;
        let c = edges[e][2];

        let mut ru: i64 = 0;
        if dist[u] <= maxMoves {
            ru = maxMoves - dist[u];
        }

        let mut rv: i64 = 0;
        if dist[v] <= maxMoves {
            rv = maxMoves - dist[v];
        }

        let mut reach = ru + rv;
        if reach > c {
            reach = c;
        }

        ans += reach;

        e += 1;
    }

    ans
}
