pub fn root_count(edges: &[Vec<i64>], guesses: &[Vec<i64>], k: i64) -> i64 {
    let n: usize = edges.len() + 1;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        adj.push(Vec::new());
        i += 1;
    }

    i = 0;
    while i < edges.len() {
        let a = edges[i][0];
        let b = edges[i][1];
        adj[a as usize].push(b);
        adj[b as usize].push(a);
        i += 1;
    }

    let mut parent: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        parent.push(-1);
        i += 1;
    }

    let mut order: Vec<i64> = Vec::new();
    order.push(0);

    let mut head: usize = 0;
    while head < order.len() {
        let u = order[head];
        let ui = u as usize;

        let mut j: usize = 0;
        while j < adj[ui].len() {
            let v = adj[ui][j];
            if v != parent[ui] {
                parent[v as usize] = u;
                order.push(v);
            }
            j += 1;
        }

        head += 1;
    }

    let mut down: Vec<i64> = Vec::new();
    let mut up: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        down.push(0);
        up.push(0);
        i += 1;
    }

    let mut root0_count: i64 = 0;
    i = 0;
    while i < guesses.len() {
        let u = guesses[i][0];
        let v = guesses[i][1];
        let ui = u as usize;
        let vi = v as usize;

        if parent[vi] == u {
            down[vi] = 1;
            root0_count += 1;
        } else if parent[ui] == v {
            up[ui] = 1;
        }

        i += 1;
    }

    let mut cnt: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        cnt.push(0);
        i += 1;
    }
    cnt[0] = root0_count;

    let mut idx: usize = 0;
    while idx < order.len() {
        let u = order[idx];
        if u != 0 {
            let ui = u as usize;
            let p = parent[ui];
            cnt[ui] = cnt[p as usize] - down[ui] + up[ui];
        }
        idx += 1;
    }

    let mut ans: i64 = 0;
    i = 0;
    while i < n {
        if cnt[i] >= k {
            ans += 1;
        }
        i += 1;
    }

    ans
}
