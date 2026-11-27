pub fn time_taken(edges: &[Vec<i64>]) -> Vec<i64> {
    let n = edges.len() + 1;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i = 0usize;
    while i < n {
        adj.push(Vec::new());
        i += 1;
    }

    i = 0usize;
    while i < edges.len() {
        let u_i = edges[i][0];
        let v_i = edges[i][1];
        let u = u_i as usize;
        let v = v_i as usize;
        adj[u].push(v_i);
        adj[v].push(u_i);
        i += 1;
    }

    let mut parent: Vec<i64> = Vec::new();
    i = 0usize;
    while i < n {
        parent.push(-1);
        i += 1;
    }
    parent[0] = -2;

    let mut order: Vec<i64> = Vec::new();
    order.push(0);

    let mut idx = 0usize;
    while idx < order.len() {
        let u_i = order[idx];
        let u = u_i as usize;
        let deg = adj[u].len();

        let mut j = 0usize;
        while j < deg {
            let v_i = adj[u][j];
            let v = v_i as usize;
            if parent[v] == -1 {
                parent[v] = u_i;
                order.push(v_i);
            }
            j += 1;
        }

        idx += 1;
    }

    let mut down: Vec<i64> = Vec::new();
    i = 0usize;
    while i < n {
        down.push(0);
        i += 1;
    }

    idx = order.len();
    while idx > 0 {
        idx -= 1;
        let u_i = order[idx];
        let u = u_i as usize;
        let deg = adj[u].len();

        let mut best: i64 = 0;
        let mut j = 0usize;
        while j < deg {
            let v_i = adj[u][j];
            let v = v_i as usize;
            if parent[v] == u_i {
                let c: i64 = if v_i % 2 == 0 { 2 } else { 1 };
                let cand = c + down[v];
                if cand > best {
                    best = cand;
                }
            }
            j += 1;
        }

        down[u] = best;
    }

    let mut up: Vec<i64> = Vec::new();
    let mut ans: Vec<i64> = Vec::new();
    i = 0usize;
    while i < n {
        up.push(0);
        ans.push(0);
        i += 1;
    }

    let mut oi = 0usize;
    while oi < order.len() {
        let u_i = order[oi];
        let u = u_i as usize;

        let mut best_ans = down[u];
        if up[u] > best_ans {
            best_ans = up[u];
        }
        ans[u] = best_ans;

        let deg = adj[u].len();

        let mut max1: i64 = -1;
        let mut max2: i64 = -1;
        let mut best_child: i64 = -1;

        let mut j = 0usize;
        while j < deg {
            let v_i = adj[u][j];
            let v = v_i as usize;
            if parent[v] == u_i {
                let c: i64 = if v_i % 2 == 0 { 2 } else { 1 };
                let val = c + down[v];

                if val > max1 {
                    max2 = max1;
                    max1 = val;
                    best_child = v_i;
                } else if val > max2 {
                    max2 = val;
                }
            }
            j += 1;
        }

        let c_u: i64 = if u_i % 2 == 0 { 2 } else { 1 };

        j = 0usize;
        while j < deg {
            let v_i = adj[u][j];
            let v = v_i as usize;
            if parent[v] == u_i {
                let mut best_excl: i64 = 0;

                if up[u] > best_excl {
                    best_excl = up[u];
                }

                let sibling_best = if v_i == best_child { max2 } else { max1 };
                if sibling_best > best_excl {
                    best_excl = sibling_best;
                }

                up[v] = c_u + best_excl;
            }
            j += 1;
        }

        oi += 1;
    }

    ans
}
