pub fn can_finish(numCourses: i64, prerequisites: &[Vec<i64>]) -> bool {
    let n: usize = numCourses as usize;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut indegree: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        indegree.push(0);
        i += 1;
    }

    let m: usize = prerequisites.len();
    let mut k: usize = 0;
    while k < m {
        let a: i64 = prerequisites[k][0];
        let b: i64 = prerequisites[k][1];

        let ai: usize = a as usize;
        let bi: usize = b as usize;

        adj[bi].push(a);
        indegree[ai] += 1;

        k += 1;
    }

    let mut queue: Vec<i64> = Vec::new();

    let mut idx: usize = 0;
    while idx < n {
        if indegree[idx] == 0 {
            queue.push(idx as i64);
        }
        idx += 1;
    }

    let mut head: usize = 0;
    let mut processed: i64 = 0;

    while head < queue.len() {
        let u_i: i64 = queue[head];
        let u: usize = u_i as usize;
        head += 1;
        processed += 1;

        let mut j: usize = 0;
        let len: usize = adj[u].len();
        while j < len {
            let v_i: i64 = adj[u][j];
            let v: usize = v_i as usize;

            indegree[v] -= 1;
            if indegree[v] == 0 {
                queue.push(v_i);
            }

            j += 1;
        }
    }

    processed == numCourses
}
