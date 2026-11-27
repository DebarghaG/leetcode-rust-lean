fn get_lca(
    mut a: usize,
    mut b: usize,
    depth: &[i64],
    up: &[i64],
    log: usize,
    n: usize,
) -> usize {
    if depth[a] < depth[b] {
        let tmp = a;
        a = b;
        b = tmp;
    }

    let diff = depth[a] - depth[b];
    let mut bit: usize = 0;
    let mut p: i64 = 1;
    while bit < log {
        if (diff / p) % 2 == 1 {
            a = up[bit * n + a] as usize;
        }
        p = p * 2;
        bit += 1;
    }

    if a == b {
        return a;
    }

    let mut k = log;
    while k > 0 {
        k -= 1;
        let pa = up[k * n + a] as usize;
        let pb = up[k * n + b] as usize;
        if pa != pb {
            a = pa;
            b = pb;
        }
    }

    return up[a] as usize;
}

pub fn min_operations_queries(n: i64, edges: &[Vec<i64>], queries: &[Vec<i64>]) -> Vec<i64> {
    let n_usize = n as usize;
    let log: usize = 15;
    let num_w: usize = 32;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        adj.push(Vec::new());
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let u = edges[e][0] as usize;
        let v = edges[e][1] as usize;
        let w = edges[e][2];

        let code1 = (v as i64) * 32 + w;
        let code2 = (u as i64) * 32 + w;

        adj[u].push(code1);
        adj[v].push(code2);

        e += 1;
    }

    let up_size = log * n_usize;
    let mut up: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < up_size {
        up.push(0);
        i += 1;
    }

    let mut depth: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        depth.push(0);
        i += 1;
    }

    let counts_size = n_usize * num_w;
    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < counts_size {
        counts.push(0);
        i += 1;
    }

    let mut stack: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        stack.push(0);
        i += 1;
    }

    let mut top: usize = 0;
    stack[top] = 0;
    top = top + 1;

    while top > 0 {
        top = top - 1;
        let u = stack[top] as usize;
        let parent_u = up[u] as usize;

        let mut ei: usize = 0;
        while ei < adj[u].len() {
            let code = adj[u][ei];
            let v = (code / 32) as usize;
            let w = (code % 32) as usize;

            if v != parent_u {
                up[v] = u as i64;
                depth[v] = depth[u] + 1;

                let mut level: usize = 1;
                while level < log {
                    let mid = up[(level - 1) * n_usize + v] as usize;
                    let val = up[(level - 1) * n_usize + mid];
                    up[level * n_usize + v] = val;
                    level += 1;
                }

                let mut c: usize = 0;
                while c < num_w {
                    let val = counts[u * num_w + c];
                    counts[v * num_w + c] = val;
                    c += 1;
                }
                counts[v * num_w + w] = counts[v * num_w + w] + 1;

                stack[top] = v as i64;
                top = top + 1;
            }

            ei += 1;
        }
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut qi: usize = 0;
    while qi < queries.len() {
        let a = queries[qi][0] as usize;
        let b = queries[qi][1] as usize;

        let l = get_lca(a, b, &depth, &up, log, n_usize);
        let path_len = depth[a] + depth[b] - 2 * depth[l];

        let mut max_count: i64 = 0;
        let mut c: usize = 0;
        while c < num_w {
            let val = counts[a * num_w + c] + counts[b * num_w + c]
                - 2 * counts[l * num_w + c];
            if val > max_count {
                max_count = val;
            }
            c += 1;
        }

        ans.push(path_len - max_count);
        qi += 1;
    }

    ans
}
