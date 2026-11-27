pub fn max_k_divisible_components(n: i64, edges: &[Vec<i64>], values: &[i64], k: i64) -> i64 {
    let n_us = n as usize;

    // Build a flat adjacency list.
    // For each directed edge, to[e] is the destination and next[e] is the next edge index.
    let mut head: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n_us {
        head.push(-1);
        i += 1;
    }

    let mut to: Vec<i64> = Vec::new();
    let mut next: Vec<i64> = Vec::new();

    let m = edges.len();
    let mut e: usize = 0;
    while e < m {
        let a = edges[e][0];
        let b = edges[e][1];
        let au = a as usize;
        let bu = b as usize;

        let idx_a = to.len() as i64;
        to.push(b);
        next.push(head[au]);
        head[au] = idx_a;

        let idx_b = to.len() as i64;
        to.push(a);
        next.push(head[bu]);
        head[bu] = idx_b;

        e += 1;
    }

    // Root the tree at node 0 and produce a preorder traversal.
    let mut parent: Vec<i64> = Vec::new();
    i = 0;
    while i < n_us {
        parent.push(-1);
        i += 1;
    }

    let mut order: Vec<i64> = Vec::new();
    let mut stack: Vec<i64> = Vec::new();

    if n_us > 0 {
        stack.push(0);
    }

    while stack.len() > 0 {
        let v = stack[stack.len() - 1];
        stack.pop();
        order.push(v);

        let vu = v as usize;
        let mut eidx = head[vu];
        while eidx != -1 {
            let eu = eidx as usize;
            let w = to[eu];
            let wu = w as usize;

            if w != parent[vu] {
                parent[wu] = v;
                stack.push(w);
            }

            eidx = next[eu];
        }
    }

    // Process nodes in reverse preorder, i.e. children before parents.
    let mut sums: Vec<i64> = Vec::new();
    i = 0;
    while i < n_us {
        sums.push(values[i]);
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut oi = order.len();

    while oi > 0 {
        oi -= 1;
        let v = order[oi];
        let vu = v as usize;
        let s = sums[vu];

        if s % k == 0 {
            ans += 1;
        }

        let pv = parent[vu];
        if pv >= 0 {
            let pu = pv as usize;
            sums[pu] += s;
        }
    }

    ans
}
