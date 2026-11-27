pub fn number_of_good_paths(vals: &[i64], edges: &[Vec<i64>]) -> i64 {
    let n = vals.len();
    if n == 0 {
        return 0;
    }

    // Build adjacency list.
    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < n {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    let mut e = 0;
    while e < edges.len() {
        let a = edges[e][0];
        let b = edges[e][1];
        let au = a as usize;
        let bu = b as usize;
        adj[au].push(b);
        adj[bu].push(a);
        e += 1;
    }

    // Counting sort of node indices by vals.
    let mut max_val: i64 = 0;
    i = 0;
    while i < n {
        if vals[i] > max_val {
            max_val = vals[i];
        }
        i += 1;
    }

    let m = (max_val + 1) as usize;
    let mut count: Vec<i64> = Vec::new();
    i = 0;
    while i < m {
        count.push(0);
        i += 1;
    }

    i = 0;
    while i < n {
        let v = vals[i] as usize;
        count[v] = count[v] + 1;
        i += 1;
    }

    let mut v = 1;
    while v < m {
        count[v] = count[v] + count[v - 1];
        v += 1;
    }

    let mut order: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        order.push(0);
        i += 1;
    }

    let mut idx: i64 = (n as i64) - 1;
    while idx >= 0 {
        let ii = idx as usize;
        let val = vals[ii] as usize;
        count[val] = count[val] - 1;
        let pos = count[val] as usize;
        order[pos] = ii as i64;
        idx -= 1;
    }

    // DSU arrays.
    let mut parent: Vec<i64> = Vec::new();
    let mut size: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        parent.push(i as i64);
        size.push(1);
        i += 1;
    }

    // Temporary counts of current-value nodes per component.
    let mut cnt: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        cnt.push(0);
        i += 1;
    }

    let mut ans: i64 = n as i64;

    let mut pos_group = 0;
    while pos_group < n {
        let start = pos_group;
        let cur_val = vals[order[start] as usize];

        let mut end = start + 1;
        while end < n && vals[order[end] as usize] == cur_val {
            end += 1;
        }

        // Union each current-value node with all neighbors whose value is <= cur_val.
        let mut k = start;
        while k < end {
            let u_i = order[k];
            let u = u_i as usize;
            let row = &adj[u];

            let mut t = 0;
            while t < row.len() {
                let v_i = row[t];
                let v = v_i as usize;

                if vals[v] <= vals[u] {
                    let mut ra = u_i;
                    while parent[ra as usize] != ra {
                        ra = parent[ra as usize];
                    }

                    let mut rb = v_i;
                    while parent[rb as usize] != rb {
                        rb = parent[rb as usize];
                    }

                    if ra != rb {
                        let ra_u = ra as usize;
                        let rb_u = rb as usize;

                        if size[ra_u] < size[rb_u] {
                            parent[ra_u] = rb;
                            size[rb_u] = size[rb_u] + size[ra_u];
                        } else {
                            parent[rb_u] = ra;
                            size[ra_u] = size[ra_u] + size[rb_u];
                        }
                    }
                }

                t += 1;
            }

            k += 1;
        }

        // Count pairs of current-value nodes in the same component.
        let mut touched: Vec<i64> = Vec::new();

        k = start;
        while k < end {
            let u_i = order[k];

            let mut r = u_i;
            while parent[r as usize] != r {
                r = parent[r as usize];
            }

            let r_u = r as usize;
            if cnt[r_u] == 0 {
                touched.push(r);
            }
            cnt[r_u] = cnt[r_u] + 1;

            k += 1;
        }

        let mut t = 0;
        while t < touched.len() {
            let r = touched[t] as usize;
            let c = cnt[r];
            ans = ans + c * (c - 1) / 2;
            cnt[r] = 0;
            t += 1;
        }

        pos_group = end;
    }

    ans
}
