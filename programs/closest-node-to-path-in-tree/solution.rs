pub fn closest_node(n: i64, edges: &[Vec<i64>], query: &[Vec<i64>]) -> Vec<i64> {
    let nn = n as usize;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < nn {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    let edge_count = edges.len();
    i = 0;
    while i < edge_count {
        let a = edges[i][0] as usize;
        let b = edges[i][1] as usize;
        adj[a].push(edges[i][1]);
        adj[b].push(edges[i][0]);
        i += 1;
    }

    let mut dist: Vec<Vec<i64>> = Vec::new();
    i = 0;
    while i < nn {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < nn {
            row.push(-1);
            j += 1;
        }
        dist.push(row);
        i += 1;
    }

    let mut s = 0;
    while s < nn {
        dist[s][s] = 0;

        let mut stack: Vec<i64> = Vec::new();
        stack.push(s as i64);

        while stack.len() > 0 {
            let top = stack.len() - 1;
            let u_value = stack[top];
            stack.pop();

            let u = u_value as usize;
            let du = dist[s][u];
            let degree = adj[u].len();

            let mut k = 0;
            while k < degree {
                let v_value = adj[u][k];
                let v = v_value as usize;

                if dist[s][v] < 0 {
                    dist[s][v] = du + 1;
                    stack.push(v_value);
                }

                k += 1;
            }
        }

        s += 1;
    }

    let mut answer: Vec<i64> = Vec::new();
    let qlen = query.len();

    i = 0;
    while i < qlen {
        let start = query[i][0] as usize;
        let end = query[i][1] as usize;
        let node = query[i][2] as usize;

        let path_len = dist[start][end];
        let mut best = -1;
        let mut best_dist = 1000000000;

        let mut v = 0;
        while v < nn {
            if dist[start][v] + dist[v][end] == path_len {
                let d = dist[v][node];
                if d < best_dist {
                    best_dist = d;
                    best = v as i64;
                }
            }
            v += 1;
        }

        answer.push(best);
        i += 1;
    }

    answer
}
