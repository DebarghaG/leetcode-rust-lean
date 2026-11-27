pub fn shortest_path_length(graph: &[Vec<i64>]) -> i64 {
    let n = graph.len();

    if n <= 1 {
        return 0;
    }

    let n_i = n as i64;
    let state_count = (1usize << n) * n;

    let mut dist: Vec<i64> = Vec::new();
    let mut idx = 0usize;
    while idx < state_count {
        dist.push(-1);
        idx += 1;
    }

    let mut queue: Vec<i64> = Vec::new();

    let mut i = 0usize;
    while i < n {
        let mask = 1usize << i;
        let flat = mask * n + i;
        dist[flat] = 0;
        queue.push(flat as i64);
        i += 1;
    }

    let full = (1usize << n) - 1;
    let mut head = 0usize;

    while head < queue.len() {
        let code = queue[head];
        head += 1;

        let mask_i = code / n_i;
        let node_i = code % n_i;
        let mask = mask_i as usize;
        let node = node_i as usize;

        let cur = mask * n + node;
        let d = dist[cur];

        if mask == full {
            return d;
        }

        let row = &graph[node];
        let mut k = 0usize;

        while k < row.len() {
            let next_node = row[k] as usize;
            let next_mask = mask | (1usize << next_node);
            let next_flat = next_mask * n + next_node;

            if dist[next_flat] == -1 {
                dist[next_flat] = d + 1;
                queue.push(next_flat as i64);
            }

            k += 1;
        }
    }

    -1
}
