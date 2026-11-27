pub fn minimum_fuel_cost(roads: &[Vec<i64>], seats: i64) -> i64 {
    let n = roads.len() + 1;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    i = 0;
    while i < roads.len() {
        let a = roads[i][0] as usize;
        let b = roads[i][1] as usize;
        let av = roads[i][0];
        let bv = roads[i][1];
        adj[a].push(bv);
        adj[b].push(av);
        i += 1;
    }

    let mut parent: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        parent.push(-2);
        i += 1;
    }

    parent[0] = -1;

    let mut order: Vec<i64> = Vec::new();
    order.push(0);
    let mut head: usize = 0;

    while head < order.len() {
        let u = order[head];
        head += 1;

        let ui = u as usize;
        let row = &adj[ui];

        let mut j: usize = 0;
        while j < row.len() {
            let v = row[j];
            let vi = v as usize;

            if parent[vi] == -2 {
                parent[vi] = u;
                order.push(v);
            }

            j += 1;
        }
    }

    let mut subtree_size: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        subtree_size.push(1);
        i += 1;
    }

    let mut total: i64 = 0;
    let mut k: usize = order.len();

    while k > 0 {
        k -= 1;

        let u = order[k];
        let ui = u as usize;
        let p = parent[ui];

        if p != -1 {
            total += (subtree_size[ui] + seats - 1) / seats;
            let pi = p as usize;
            subtree_size[pi] += subtree_size[ui];
        }
    }

    total
}
