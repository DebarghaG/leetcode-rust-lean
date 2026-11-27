pub fn shortest_path_with_hops(n: i64, edges: &[Vec<i64>], s: i64, d: i64, k: i64) -> i64 {
    let nn = n as usize;
    let inf: i64 = 1_000_000_000_000_000_000;

    // Build adjacency list: for each node, pairs [neighbor, weight, ...].
    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i = 0usize;
    while i < nn {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    let mut ei = 0usize;
    while ei < edges.len() {
        let e = &edges[ei];
        let u = e[0] as usize;
        let v = e[1] as usize;
        let w = e[2];

        adj[u].push(v as i64);
        adj[u].push(w);
        adj[v].push(u as i64);
        adj[v].push(w);

        ei += 1;
    }

    // If we may zero at least n - 1 edges, we can zero every edge of a simple path.
    let mut hops = k;
    if hops < 0 {
        hops = 0;
    }
    if hops >= n - 1 {
        return 0;
    }

    // dist = shortest distances with currently allowed zero-hops.
    let mut dist: Vec<i64> = Vec::new();
    let mut j = 0usize;
    while j < nn {
        dist.push(inf);
        j += 1;
    }
    dist[s as usize] = 0;

    // Initial Dijkstra with no zeroed edges.
    let mut used: Vec<bool> = Vec::new();
    let mut u0 = 0usize;
    while u0 < nn {
        used.push(false);
        u0 += 1;
    }

    let mut cnt = 0usize;
    while cnt < nn {
        let mut best = inf;
        let mut u = nn;
        let mut v = 0usize;
        while v < nn {
            if !used[v] && dist[v] < best {
                best = dist[v];
                u = v;
            }
            v += 1;
        }
        if u == nn {
            break;
        }

        used[u] = true;
        let row = &adj[u];
        let mut idx = 0usize;
        while idx < row.len() {
            let v2 = row[idx] as usize;
            let w = row[idx + 1];
            let nd = dist[u] + w;
            if nd < dist[v2] {
                dist[v2] = nd;
            }
            idx += 2;
        }

        cnt += 1;
    }

    let mut step: i64 = 1;
    while step <= hops {
        // cur[v] = best cost to v after choosing the last zeroed edge to end at v,
        // or after using fewer than this many zeroed edges.
        let mut cur: Vec<i64> = Vec::new();
        let mut a = 0usize;
        while a < nn {
            cur.push(dist[a]);
            a += 1;
        }

        let mut u = 0usize;
        while u < nn {
            let row = &adj[u];
            let pu = dist[u];
            let mut idx = 0usize;
            while idx < row.len() {
                let v = row[idx] as usize;
                // Zero the edge u -> v.
                if pu < cur[v] {
                    cur[v] = pu;
                }
                idx += 2;
            }
            u += 1;
        }

        // Multi-source Dijkstra over positive edges from all current starting values.
        let mut used2: Vec<bool> = Vec::new();
        let mut b = 0usize;
        while b < nn {
            used2.push(false);
            b += 1;
        }

        let mut cnt2 = 0usize;
        while cnt2 < nn {
            let mut best = inf;
            let mut u = nn;
            let mut v = 0usize;
            while v < nn {
                if !used2[v] && cur[v] < best {
                    best = cur[v];
                    u = v;
                }
                v += 1;
            }
            if u == nn {
                break;
            }

            used2[u] = true;
            let row = &adj[u];
            let mut idx = 0usize;
            while idx < row.len() {
                let v2 = row[idx] as usize;
                let w = row[idx + 1];
                let nd = cur[u] + w;
                if nd < cur[v2] {
                    cur[v2] = nd;
                }
                idx += 2;
            }

            cnt2 += 1;
        }

        dist = cur;
        step += 1;
    }

    dist[d as usize]
}
