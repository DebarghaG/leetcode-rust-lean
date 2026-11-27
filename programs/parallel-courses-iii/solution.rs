pub fn minimum_time(n: i64, relations: &[Vec<i64>], time: &[i64]) -> i64 {
    let n_usize = n as usize;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    let mut indeg: Vec<i64> = Vec::new();
    i = 0;
    while i < n_usize {
        indeg.push(0);
        i += 1;
    }

    let mut r: usize = 0;
    while r < relations.len() {
        let p = relations[r][0] - 1;
        let q = relations[r][1] - 1;
        let pu = p as usize;
        let qu = q as usize;

        adj[pu].push(q);
        indeg[qu] += 1;

        r += 1;
    }

    let mut dp: Vec<i64> = Vec::new();
    i = 0;
    while i < n_usize {
        dp.push(time[i]);
        i += 1;
    }

    let mut queue: Vec<i64> = Vec::new();
    i = 0;
    while i < n_usize {
        if indeg[i] == 0 {
            queue.push(i as i64);
        }
        i += 1;
    }

    let mut head: usize = 0;
    while head < queue.len() {
        let u = queue[head];
        let uu = u as usize;
        let base = dp[uu];

        let row_len = adj[uu].len();
        let row = &adj[uu];

        let mut j: usize = 0;
        while j < row_len {
            let v = row[j] as usize;
            let candidate = base + time[v];

            if dp[v] < candidate {
                dp[v] = candidate;
            }

            indeg[v] -= 1;
            if indeg[v] == 0 {
                queue.push(v as i64);
            }

            j += 1;
        }

        head += 1;
    }

    let mut ans: i64 = 0;
    i = 0;
    while i < n_usize {
        if dp[i] > ans {
            ans = dp[i];
        }
        i += 1;
    }

    ans
}
