pub fn network_becomes_idle(edges: &[Vec<i64>], patience: &[i64]) -> i64 {
    let n = patience.len();

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let u_i = edges[e][0];
        let v_i = edges[e][1];
        let u = u_i as usize;
        let v = v_i as usize;

        adj[u].push(v_i);
        adj[v].push(u_i);

        e += 1;
    }

    let mut dist: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        dist.push(-1);
        i += 1;
    }
    dist[0] = 0;

    let mut queue: Vec<i64> = Vec::new();
    queue.push(0);

    let mut head: usize = 0;
    while head < queue.len() {
        let u_i = queue[head];
        let u = u_i as usize;
        head += 1;

        let row = &adj[u];
        let row_len = row.len();
        let mut j: usize = 0;
        while j < row_len {
            let v_i = row[j];
            let v = v_i as usize;

            if dist[v] == -1 {
                let nd = dist[u] + 1;
                dist[v] = nd;
                queue.push(v_i);
            }

            j += 1;
        }
    }

    let mut ans: i64 = 0;
    let mut s: usize = 1;
    while s < n {
        let d = dist[s];
        let p = patience[s];

        let last_sent = ((2 * d - 1) / p) * p;
        let idle_time = last_sent + 2 * d + 1;

        if idle_time > ans {
            ans = idle_time;
        }

        s += 1;
    }

    ans
}
