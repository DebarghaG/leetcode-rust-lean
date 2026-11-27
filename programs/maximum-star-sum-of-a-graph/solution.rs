pub fn max_star_sum(vals: &[i64], edges: &[Vec<i64>], k: i64) -> i64 {
    let n = vals.len();

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i = 0usize;
    while i < n {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    let mut e = 0usize;
    while e < edges.len() {
        let a = edges[e][0] as usize;
        let b = edges[e][1] as usize;

        let va = vals[a];
        let vb = vals[b];

        if vb > 0 {
            adj[a].push(vb);
        }
        if va > 0 {
            adj[b].push(va);
        }

        e += 1;
    }

    let mut ans = vals[0];
    let mut center = 0usize;
    while center < n {
        let row = &mut adj[center];
        row.sort();

        let mut sum = vals[center];
        let len = row.len();
        let mut take = 0usize;

        while (take as i64) < k && take < len {
            let idx = len - 1 - take;
            sum += row[idx];
            take += 1;
        }

        if sum > ans {
            ans = sum;
        }

        center += 1;
    }

    ans
}
