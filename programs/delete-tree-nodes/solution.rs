pub fn delete_tree_nodes(nodes: i64, parent: &[i64], value: &[i64]) -> i64 {
    let n = nodes as usize;
    if n == 0 {
        return 0;
    }

    let mut children: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < n {
        children.push(Vec::new());
        i += 1;
    }

    i = 0;
    while i < n {
        let p = parent[i];
        if p >= 0 {
            let pi = p as usize;
            children[pi].push(i as i64);
        }
        i += 1;
    }

    let mut order: Vec<i64> = Vec::new();
    let mut stack: Vec<i64> = Vec::new();
    stack.push(0);

    while stack.len() > 0 {
        let u = stack[stack.len() - 1];
        stack.pop();
        order.push(u);

        let ui = u as usize;
        let row = &children[ui];
        let mut j = 0;
        while j < row.len() {
            stack.push(row[j]);
            j += 1;
        }
    }

    let mut sums: Vec<i64> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        sums.push(0);
        counts.push(0);
        i += 1;
    }

    let mut oi = order.len();
    while oi > 0 {
        oi -= 1;
        let u = order[oi];
        let ui = u as usize;

        let mut s = value[ui];
        let mut c: i64 = 1;

        let row = &children[ui];
        let mut j = 0;
        while j < row.len() {
            let v = row[j] as usize;
            s = s + sums[v];
            c = c + counts[v];
            j += 1;
        }

        if s == 0 {
            c = 0;
        }

        sums[ui] = s;
        counts[ui] = c;
    }

    counts[0]
}
