pub fn distance_to_cycle(n: i64, edges: &[Vec<i64>]) -> Vec<i64> {
    let n_us = n as usize;

    // Build adjacency list.
    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n_us {
        adj.push(Vec::new());
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let u = edges[e][0];
        let v = edges[e][1];
        let uu = u as usize;
        let vv = v as usize;
        adj[uu].push(v);
        adj[vv].push(u);
        e += 1;
    }

    // Degrees used for leaf pruning.
    let mut deg: Vec<i64> = Vec::new();
    i = 0;
    while i < n_us {
        deg.push(adj[i].len() as i64);
        i += 1;
    }

    // Find all cycle nodes by repeatedly removing degree-1 nodes.
    let mut q: Vec<i64> = Vec::new();
    i = 0;
    while i < n_us {
        if deg[i] == 1 {
            q.push(i as i64);
        }
        i += 1;
    }

    let mut head: usize = 0;
    while head < q.len() {
        let u_i = q[head];
        head += 1;
        let u = u_i as usize;

        if deg[u] != 1 {
            continue;
        }

        deg[u] = 0;

        let mut k: usize = 0;
        while k < adj[u].len() {
            let v_i = adj[u][k];
            let v = v_i as usize;

            if deg[v] > 0 {
                deg[v] -= 1;
                if deg[v] == 1 {
                    q.push(v_i);
                }
            }

            k += 1;
        }
    }

    // Multi-source BFS from all cycle nodes.
    let mut dist: Vec<i64> = Vec::new();
    i = 0;
    while i < n_us {
        dist.push(-1);
        i += 1;
    }

    let mut bfs: Vec<i64> = Vec::new();
    i = 0;
    while i < n_us {
        if deg[i] > 0 {
            dist[i] = 0;
            bfs.push(i as i64);
        }
        i += 1;
    }

    head = 0;
    while head < bfs.len() {
        let u_i = bfs[head];
        head += 1;
        let u = u_i as usize;
        let du = dist[u];

        let mut k: usize = 0;
        while k < adj[u].len() {
            let v_i = adj[u][k];
            let v = v_i as usize;

            if dist[v] == -1 {
                dist[v] = du + 1;
                bfs.push(v_i);
            }

            k += 1;
        }
    }

    dist
}
