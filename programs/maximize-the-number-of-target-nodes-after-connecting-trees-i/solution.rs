fn build_adj(edges: &[Vec<i64>], n: usize) -> Vec<Vec<i64>> {
    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let a_val = edges[e][0];
        let b_val = edges[e][1];
        let a = a_val as usize;
        let b = b_val as usize;
        adj[a].push(b_val);
        adj[b].push(a_val);
        e += 1;
    }

    adj
}

fn count_within(adj: &[Vec<i64>], start: usize, max_dist: i64) -> i64 {
    if max_dist < 0 {
        return 0;
    }

    let n = adj.len();

    let mut dist: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        dist.push(-1);
        i += 1;
    }

    let mut queue: Vec<i64> = Vec::new();
    queue.push(start as i64);
    dist[start] = 0;

    let mut head: usize = 0;
    let mut count: i64 = 1;

    while head < queue.len() {
        let u_val = queue[head];
        let u = u_val as usize;
        head += 1;

        let d = dist[u];
        if d < max_dist {
            let row = &adj[u];
            let mut j: usize = 0;
            while j < row.len() {
                let v_val = row[j];
                let v = v_val as usize;
                if dist[v] == -1 {
                    dist[v] = d + 1;
                    count += 1;
                    queue.push(v_val);
                }
                j += 1;
            }
        }
    }

    count
}

pub fn max_target_nodes(edges1: &[Vec<i64>], edges2: &[Vec<i64>], k: i64) -> Vec<i64> {
    let n = edges1.len() + 1;
    let m = edges2.len() + 1;

    let adj1 = build_adj(edges1, n);
    let adj2 = build_adj(edges2, m);

    let mut best2: i64 = 0;
    if k >= 1 {
        let limit = k - 1;
        let mut j: usize = 0;
        while j < m {
            let c = count_within(&adj2, j, limit);
            if c > best2 {
                best2 = c;
            }
            j += 1;
        }
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let c1 = count_within(&adj1, i, k);
        ans.push(c1 + best2);
        i += 1;
    }

    ans
}
