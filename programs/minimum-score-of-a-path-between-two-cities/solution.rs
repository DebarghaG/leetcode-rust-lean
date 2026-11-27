pub fn min_score(n: i64, roads: &[Vec<i64>]) -> i64 {
    let nn = n as usize;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i <= nn {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    let mut r: usize = 0;
    while r < roads.len() {
        let a = roads[r][0] as usize;
        let b = roads[r][1] as usize;
        let w = roads[r][2];

        adj[a].push(b as i64);
        adj[a].push(w);
        adj[b].push(a as i64);
        adj[b].push(w);

        r += 1;
    }

    let mut visited: Vec<bool> = Vec::new();
    i = 0;
    while i <= nn {
        visited.push(false);
        i += 1;
    }

    let mut q: Vec<i64> = Vec::new();
    visited[1] = true;
    q.push(1);

    let mut head: usize = 0;
    let mut ans: i64 = 1000000000;

    while head < q.len() {
        let u = q[head] as usize;
        head += 1;

        let mut j: usize = 0;
        while j < adj[u].len() {
            let v_i = adj[u][j];
            let w = adj[u][j + 1];

            if w < ans {
                ans = w;
            }

            let v = v_i as usize;
            if !visited[v] {
                visited[v] = true;
                q.push(v_i);
            }

            j += 2;
        }
    }

    ans
}
