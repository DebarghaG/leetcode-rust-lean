pub fn min_edge_reversals(n: i64, edges: &[Vec<i64>]) -> Vec<i64> {
    let n_us = n as usize;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut cost: Vec<Vec<i64>> = Vec::new();

    let mut i: usize = 0;
    while i < n_us {
        adj.push(Vec::new());
        cost.push(Vec::new());
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let u = edges[e][0];
        let v = edges[e][1];
        let ui = u as usize;
        let vi = v as usize;

        // Traversing u -> v when u is the parent costs 0.
        adj[ui].push(v);
        cost[ui].push(0);

        // Traversing v -> u when v is the parent costs 1.
        adj[vi].push(u);
        cost[vi].push(1);

        e += 1;
    }

    let mut parent: Vec<i64> = Vec::new();
    let mut parent_cost: Vec<i64> = Vec::new();

    i = 0;
    while i < n_us {
        parent.push(-1);
        parent_cost.push(0);
        i += 1;
    }

    parent[0] = -2;

    let mut queue: Vec<i64> = Vec::new();
    queue.push(0);

    let mut head: usize = 0;
    let mut base: i64 = 0;

    while head < queue.len() {
        let u = queue[head];
        head += 1;

        let ui = u as usize;
        let mut k: usize = 0;

        while k < adj[ui].len() {
            let v = adj[ui][k];
            let vi = v as usize;

            if parent[vi] == -1 {
                parent[vi] = u;
                let c = cost[ui][k];
                parent_cost[vi] = c;
                base += c;
                queue.push(v);
            }

            k += 1;
        }
    }

    let mut ans: Vec<i64> = Vec::new();
    i = 0;
    while i < n_us {
        ans.push(0);
        i += 1;
    }

    ans[0] = base;

    let mut idx: usize = 0;
    while idx < queue.len() {
        let u = queue[idx];

        if u != 0 {
            let ui = u as usize;
            let p = parent[ui];
            let pi = p as usize;
            let c = parent_cost[ui];

            ans[ui] = ans[pi] + 1 - 2 * c;
        }

        idx += 1;
    }

    ans
}
