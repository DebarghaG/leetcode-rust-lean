pub fn largest_path_value(colors: &[u8], edges: &[Vec<i64>]) -> i64 {
    let n = colors.len();
    if n == 0 {
        return 0;
    }

    let mut head: Vec<i64> = Vec::new();
    let mut indeg: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        head.push(-1);
        indeg.push(0);
        i += 1;
    }

    let mut to: Vec<i64> = Vec::new();
    let mut next_edge: Vec<i64> = Vec::new();

    let mut e = 0;
    while e < edges.len() {
        let a = edges[e][0] as usize;
        let b = edges[e][1] as usize;

        to.push(b as i64);
        next_edge.push(head[a]);
        head[a] = e as i64;
        indeg[b] += 1;

        e += 1;
    }

    let mut dp: Vec<i64> = Vec::new();
    let total = n * 26;
    let mut k = 0;
    while k < total {
        dp.push(0);
        k += 1;
    }

    let mut v = 0;
    while v < n {
        let c = (colors[v] as i64 - 97) as usize;
        dp[v * 26 + c] = 1;
        v += 1;
    }

    let mut queue: Vec<i64> = Vec::new();
    v = 0;
    while v < n {
        if indeg[v] == 0 {
            queue.push(v as i64);
        }
        v += 1;
    }

    let mut qhead: usize = 0;
    let mut processed: i64 = 0;
    let mut ans: i64 = 0;

    while qhead < queue.len() {
        let vv = queue[qhead] as usize;
        qhead += 1;
        processed += 1;

        let base = vv * 26;
        let mut c = 0;
        while c < 26 {
            let val = dp[base + c];
            if val > ans {
                ans = val;
            }
            c += 1;
        }

        let mut edge_idx = head[vv];
        while edge_idx != -1 {
            let ei = edge_idx as usize;
            let u = to[ei] as usize;
            let ubase = u * 26;
            let cu = (colors[u] as i64 - 97) as usize;

            let mut col = 0;
            while col < 26 {
                let mut cand = dp[base + col];
                if col == cu {
                    cand += 1;
                }
                if cand > dp[ubase + col] {
                    dp[ubase + col] = cand;
                }
                col += 1;
            }

            indeg[u] -= 1;
            if indeg[u] == 0 {
                queue.push(u as i64);
            }

            edge_idx = next_edge[ei];
        }
    }

    if processed != n as i64 {
        return -1;
    }

    ans
}
