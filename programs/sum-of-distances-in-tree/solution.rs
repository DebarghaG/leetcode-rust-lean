pub fn sum_of_distances_in_tree(n: i64, edges: &[Vec<i64>]) -> Vec<i64> {
    let nn = n as usize;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < nn {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    let m = edges.len();
    i = 0;
    while i < m {
        let a = edges[i][0];
        let b = edges[i][1];
        let ai = a as usize;
        let bi = b as usize;
        adj[ai].push(b);
        adj[bi].push(a);
        i += 1;
    }

    let mut parent: Vec<i64> = Vec::new();
    let mut depth: Vec<i64> = Vec::new();
    let mut sizes: Vec<i64> = Vec::new();
    let mut ans: Vec<i64> = Vec::new();

    i = 0;
    while i < nn {
        parent.push(-1);
        depth.push(0);
        sizes.push(1);
        ans.push(0);
        i += 1;
    }

    if nn == 0 {
        return ans;
    }

    let mut order: Vec<i64> = Vec::new();
    order.push(0);

    let mut pos = 0;
    while pos < order.len() {
        let u_val = order[pos];
        let u = u_val as usize;
        let p = parent[u];

        let mut k = 0;
        while k < adj[u].len() {
            let v_val = adj[u][k];
            if v_val != p {
                let v = v_val as usize;
                parent[v] = u_val;
                depth[v] = depth[u] + 1;
                order.push(v_val);
            }
            k += 1;
        }

        pos += 1;
    }

    let mut sum_depth: i64 = 0;
    i = 0;
    while i < nn {
        sum_depth += depth[i];
        i += 1;
    }
    ans[0] = sum_depth;

    let mut rev = order.len();
    while rev > 0 {
        rev -= 1;
        let u_val = order[rev];
        let u = u_val as usize;
        let p = parent[u];

        if p >= 0 {
            let pu = p as usize;
            sizes[pu] += sizes[u];
        }
    }

    let mut oi = 1;
    while oi < order.len() {
        let u_val = order[oi];
        let u = u_val as usize;
        let p = parent[u];
        let pu = p as usize;

        ans[u] = ans[pu] + n - 2 * sizes[u];
        oi += 1;
    }

    ans
}
