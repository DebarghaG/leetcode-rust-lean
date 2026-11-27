pub fn most_similar(n: i64, roads: &[Vec<i64>], names: &[Vec<u8>], targetPath: &[Vec<u8>]) -> Vec<i64> {
    let n_usize = n as usize;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        let empty: Vec<i64> = Vec::new();
        adj.push(empty);
        i += 1;
    }

    let mut r: usize = 0;
    while r < roads.len() {
        let a_i = roads[r][0];
        let b_i = roads[r][1];
        let a = a_i as usize;
        let b = b_i as usize;
        adj[a].push(b_i);
        adj[b].push(a_i);
        r += 1;
    }

    let l = targetPath.len();

    let mut prev: Vec<i64> = Vec::new();
    let mut v: usize = 0;
    while v < n_usize {
        let mut cost: i64 = 0;
        if names[v][0] != targetPath[0][0]
            || names[v][1] != targetPath[0][1]
            || names[v][2] != targetPath[0][2]
        {
            cost = 1;
        }
        prev.push(cost);
        v += 1;
    }

    let mut parent: Vec<Vec<i64>> = Vec::new();

    let mut pos: usize = 1;
    while pos < l {
        let mut curr: Vec<i64> = Vec::new();
        let mut prow: Vec<i64> = Vec::new();

        let mut v2: usize = 0;
        while v2 < n_usize {
            let mut best: i64 = 1000000000;
            let mut best_prev: i64 = -1;

            let mut k: usize = 0;
            while k < adj[v2].len() {
                let u_i = adj[v2][k];
                let u = u_i as usize;
                let cand = prev[u];
                if cand < best {
                    best = cand;
                    best_prev = u_i;
                }
                k += 1;
            }

            let mut cost: i64 = 0;
            if names[v2][0] != targetPath[pos][0]
                || names[v2][1] != targetPath[pos][1]
                || names[v2][2] != targetPath[pos][2]
            {
                cost = 1;
            }

            curr.push(cost + best);
            prow.push(best_prev);
            v2 += 1;
        }

        parent.push(prow);
        prev = curr;
        pos += 1;
    }

    let mut best_end: i64 = prev[0];
    let mut end: i64 = 0;

    let mut idx_v: usize = 1;
    while idx_v < n_usize {
        if prev[idx_v] < best_end {
            best_end = prev[idx_v];
            end = idx_v as i64;
        }
        idx_v += 1;
    }

    let mut ans_rev: Vec<i64> = Vec::new();
    let mut p: usize = l - 1;
    let mut cur: i64 = end;

    while p > 0 {
        ans_rev.push(cur);
        cur = parent[p - 1][cur as usize];
        p -= 1;
    }
    ans_rev.push(cur);

    let mut ans: Vec<i64> = Vec::new();
    let mut idx: usize = ans_rev.len();
    while idx > 0 {
        idx -= 1;
        ans.push(ans_rev[idx]);
    }

    ans
}
