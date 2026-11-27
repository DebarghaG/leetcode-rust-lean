pub fn shortest_distance_after_queries(n: i64, queries: &[Vec<i64>]) -> Vec<i64> {
    let n_usize = n as usize;
    let target = (n - 1) as usize;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i = 0usize;
    while i < n_usize {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    let mut answer: Vec<i64> = Vec::new();
    let mut qi = 0usize;
    while qi < queries.len() {
        let u = queries[qi][0] as usize;
        let v = queries[qi][1];
        adj[u].push(v);

        let mut dist: Vec<i64> = Vec::new();
        let mut j = 0usize;
        while j < n_usize {
            dist.push(n + 1);
            j += 1;
        }
        dist[0] = 0;

        let mut cur = 0usize;
        while cur < n_usize {
            let d = dist[cur];
            if d <= n {
                if cur + 1 < n_usize {
                    if d + 1 < dist[cur + 1] {
                        dist[cur + 1] = d + 1;
                    }
                }

                let edge_count = adj[cur].len();
                let mut t = 0usize;
                while t < edge_count {
                    let to = adj[cur][t] as usize;
                    if d + 1 < dist[to] {
                        dist[to] = d + 1;
                    }
                    t += 1;
                }
            }
            cur += 1;
        }

        answer.push(dist[target]);
        qi += 1;
    }

    answer
}
