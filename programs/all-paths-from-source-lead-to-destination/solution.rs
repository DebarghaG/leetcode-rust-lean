pub fn leads_to_destination(n: i64, edges: &[Vec<i64>], source: i64, destination: i64) -> bool {
    let n_usize = n as usize;

    // Build adjacency list.
    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut init_i: usize = 0;
    while init_i < n_usize {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        init_i = init_i + 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let a = edges[e][0];
        let b = edges[e][1];
        let ai = a as usize;
        adj[ai].push(b);
        e = e + 1;
    }

    // Find all nodes reachable from source, and check reachable sinks.
    let mut reach: Vec<i64> = Vec::new();
    let mut r: usize = 0;
    while r < n_usize {
        reach.push(0);
        r = r + 1;
    }

    let source_u = source as usize;
    let mut queue: Vec<i64> = Vec::new();
    reach[source_u] = 1;
    queue.push(source);
    let mut reach_count: i64 = 1;

    let mut head: usize = 0;
    while head < queue.len() {
        let u = queue[head];
        let uidx = u as usize;
        head = head + 1;

        if adj[uidx].len() == 0 {
            if u != destination {
                return false;
            }
        }

        let mut j: usize = 0;
        while j < adj[uidx].len() {
            let v = adj[uidx][j];
            let vidx = v as usize;
            if reach[vidx] == 0 {
                reach[vidx] = 1;
                reach_count = reach_count + 1;
                queue.push(v);
            }
            j = j + 1;
        }
    }

    // Compute indegrees inside the reachable subgraph.
    let mut indeg: Vec<i64> = Vec::new();
    let mut d: usize = 0;
    while d < n_usize {
        indeg.push(0);
        d = d + 1;
    }

    let mut qidx: usize = 0;
    while qidx < queue.len() {
        let u = queue[qidx];
        let uidx = u as usize;
        qidx = qidx + 1;

        let mut j: usize = 0;
        while j < adj[uidx].len() {
            let v = adj[uidx][j];
            let vidx = v as usize;
            indeg[vidx] = indeg[vidx] + 1;
            j = j + 1;
        }
    }

    // Kahn's algorithm on the reachable subgraph detects reachable cycles.
    let mut q2: Vec<i64> = Vec::new();
    let mut p: usize = 0;
    while p < queue.len() {
        let u = queue[p];
        let uidx = u as usize;
        if indeg[uidx] == 0 {
            q2.push(u);
        }
        p = p + 1;
    }

    let mut processed: i64 = 0;
    let mut h2: usize = 0;
    while h2 < q2.len() {
        let u = q2[h2];
        let uidx = u as usize;
        h2 = h2 + 1;
        processed = processed + 1;

        let mut j: usize = 0;
        while j < adj[uidx].len() {
            let v = adj[uidx][j];
            let vidx = v as usize;
            indeg[vidx] = indeg[vidx] - 1;
            if indeg[vidx] == 0 {
                q2.push(v);
            }
            j = j + 1;
        }
    }

    processed == reach_count
}
