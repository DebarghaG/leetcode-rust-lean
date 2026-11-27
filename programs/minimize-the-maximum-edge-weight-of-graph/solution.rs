fn feasible(n: usize, rev_nodes: &[Vec<i64>], rev_weights: &[Vec<i64>], limit: i64) -> bool {
    let mut visited: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        visited.push(false);
        i += 1;
    }

    let mut queue: Vec<i64> = Vec::new();
    visited[0] = true;
    queue.push(0);

    let mut head: usize = 0;
    let mut count: usize = 1;

    while head < queue.len() {
        let u_i64 = queue[head];
        let u = u_i64 as usize;
        head += 1;

        let deg = rev_nodes[u].len();
        let mut j: usize = 0;
        while j < deg {
            let v_i64 = rev_nodes[u][j];
            let w = rev_weights[u][j];

            if w <= limit {
                let v = v_i64 as usize;
                if !visited[v] {
                    visited[v] = true;
                    count += 1;
                    queue.push(v_i64);
                }
            }

            j += 1;
        }
    }

    count == n
}

pub fn min_max_weight(n: i64, edges: &[Vec<i64>], threshold: i64) -> i64 {
    if n <= 1 {
        return 0;
    }
    if threshold < 1 {
        return -1;
    }

    let nn = n as usize;

    let mut rev_nodes: Vec<Vec<i64>> = Vec::new();
    let mut rev_weights: Vec<Vec<i64>> = Vec::new();

    let mut i: usize = 0;
    while i < nn {
        rev_nodes.push(Vec::new());
        rev_weights.push(Vec::new());
        i += 1;
    }

    let mut max_w: i64 = 0;
    let m = edges.len();
    let mut k: usize = 0;

    while k < m {
        let e = &edges[k];
        let a = e[0];
        let b = e[1];
        let w = e[2];

        if w > max_w {
            max_w = w;
        }

        let bi = b as usize;
        rev_nodes[bi].push(a);
        rev_weights[bi].push(w);

        k += 1;
    }

    if !feasible(nn, &rev_nodes, &rev_weights, max_w) {
        return -1;
    }

    let mut lo: i64 = 1;
    let mut hi: i64 = max_w;
    let mut ans: i64 = -1;

    while lo <= hi {
        let mid = lo + (hi - lo) / 2;

        if feasible(nn, &rev_nodes, &rev_weights, mid) {
            ans = mid;
            hi = mid - 1;
        } else {
            lo = mid + 1;
        }
    }

    ans
}
