pub fn max_output(n: i64, edges: &[Vec<i64>], price: &[i64]) -> i64 {
    let n_us = n as usize;
    let m_edges = edges.len();

    let mut deg: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n_us {
        deg.push(0);
        i += 1;
    }

    let mut e = 0usize;
    while e < m_edges {
        let a = edges[e][0];
        let b = edges[e][1];
        let ia = a as usize;
        let ib = b as usize;
        deg[ia] = deg[ia] + 1;
        deg[ib] = deg[ib] + 1;
        e += 1;
    }

    let mut offset: Vec<i64> = Vec::new();
    let mut sum = 0i64;
    i = 0;
    while i < n_us {
        offset.push(sum);
        sum = sum + deg[i];
        i += 1;
    }
    offset.push(sum);

    let mut cur: Vec<i64> = Vec::new();
    i = 0;
    while i < n_us {
        cur.push(offset[i]);
        i += 1;
    }

    let total = sum as usize;
    let mut to: Vec<i64> = Vec::new();
    i = 0;
    while i < total {
        to.push(0);
        i += 1;
    }

    e = 0;
    while e < m_edges {
        let a = edges[e][0];
        let b = edges[e][1];
        let ia = a as usize;
        let ib = b as usize;

        let pa = cur[ia] as usize;
        to[pa] = b;
        cur[ia] = cur[ia] + 1;

        let pb = cur[ib] as usize;
        to[pb] = a;
        cur[ib] = cur[ib] + 1;

        e += 1;
    }

    let mut parent: Vec<i64> = Vec::new();
    i = 0;
    while i < n_us {
        parent.push(-1);
        i += 1;
    }

    let mut order: Vec<i64> = Vec::new();
    order.push(0);

    let mut head = 0usize;
    while head < order.len() {
        let u = order[head];
        let iu = u as usize;
        let pu = parent[iu];

        let start = offset[iu] as usize;
        let end = offset[iu + 1] as usize;

        let mut p = start;
        while p < end {
            let v = to[p];
            if v != pu {
                let iv = v as usize;
                parent[iv] = u;
                order.push(v);
            }
            p += 1;
        }

        head += 1;
    }

    let mut down: Vec<i64> = Vec::new();
    i = 0;
    while i < n_us {
        down.push(0);
        i += 1;
    }

    let mut oi = order.len();
    while oi > 0 {
        oi -= 1;

        let u = order[oi];
        let iu = u as usize;

        let start = offset[iu] as usize;
        let end = offset[iu + 1] as usize;

        let mut best = 0i64;
        let mut p = start;
        while p < end {
            let v = to[p];
            let iv = v as usize;
            if parent[iv] == u {
                let val = down[iv];
                if val > best {
                    best = val;
                }
            }
            p += 1;
        }

        down[iu] = price[iu] + best;
    }

    let mut up: Vec<i64> = Vec::new();
    i = 0;
    while i < n_us {
        up.push(0);
        i += 1;
    }

    let mut ans = 0i64;
    let mut idx = 0usize;

    while idx < order.len() {
        let u = order[idx];
        let iu = u as usize;

        let start = offset[iu] as usize;
        let end = offset[iu + 1] as usize;

        let mut top1 = 0i64;
        let mut top2 = 0i64;
        let mut top_child = -1i64;

        let mut p = start;
        while p < end {
            let v = to[p];
            let iv = v as usize;
            if parent[iv] == u {
                let val = down[iv];
                if val > top1 {
                    top2 = top1;
                    top1 = val;
                    top_child = v;
                } else {
                    if val > top2 {
                        top2 = val;
                    }
                }
            }
            p += 1;
        }

        let parent_ext = if u == 0 { 0i64 } else { up[iu] };

        let mut best_ext = parent_ext;
        if top1 > best_ext {
            best_ext = top1;
        }
        if best_ext > ans {
            ans = best_ext;
        }

        p = start;
        while p < end {
            let v = to[p];
            let iv = v as usize;
            if parent[iv] == u {
                let mut child_ext = parent_ext;
                let other = if v == top_child { top2 } else { top1 };
                if other > child_ext {
                    child_ext = other;
                }
                up[iv] = price[iu] + child_ext;
            }
            p += 1;
        }

        idx += 1;
    }

    ans
}
