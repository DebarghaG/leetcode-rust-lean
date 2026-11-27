pub fn find_order(numCourses: i64, prerequisites: &[Vec<i64>]) -> Vec<i64> {
    let n = numCourses as usize;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut indeg: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        adj.push(Vec::new());
        indeg.push(0);
        i += 1;
    }

    let mut k: usize = 0;
    while k < prerequisites.len() {
        let a = prerequisites[k][0];
        let b = prerequisites[k][1];

        adj[b as usize].push(a);
        indeg[a as usize] = indeg[a as usize] + 1;

        k += 1;
    }

    let mut queue: Vec<i64> = Vec::new();

    let mut j: usize = 0;
    while j < n {
        if indeg[j] == 0 {
            queue.push(j as i64);
        }
        j += 1;
    }

    let mut order: Vec<i64> = Vec::new();
    let mut head: usize = 0;

    while head < queue.len() {
        let u = queue[head];
        head += 1;

        order.push(u);

        let u_idx = u as usize;
        let mut t: usize = 0;

        while t < adj[u_idx].len() {
            let v = adj[u_idx][t];
            let v_idx = v as usize;

            indeg[v_idx] = indeg[v_idx] - 1;

            if indeg[v_idx] == 0 {
                queue.push(v);
            }

            t += 1;
        }
    }

    if order.len() == n {
        order
    } else {
        Vec::new()
    }
}
