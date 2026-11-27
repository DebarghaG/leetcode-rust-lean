pub fn all_paths_source_target(graph: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n = graph.len();
    let mut out: Vec<Vec<i64>> = Vec::new();

    if n == 0 {
        return out;
    }

    let target: usize = n - 1;

    // Preallocated explicit DFS stacks. stack_len is the number of active frames.
    let mut stack_nodes: Vec<usize> = Vec::new();
    let mut stack_idx: Vec<usize> = Vec::new();
    let mut path: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        stack_nodes.push(0);
        stack_idx.push(0);
        path.push(0);
        i += 1;
    }

    stack_nodes[0] = 0;
    stack_idx[0] = 0;
    path[0] = 0;

    let mut stack_len: usize = 1;

    while stack_len > 0 {
        let top: usize = stack_len - 1;
        let u: usize = stack_nodes[top];

        if u == target {
            let mut p: Vec<i64> = Vec::new();
            let mut k: usize = 0;
            while k < stack_len {
                p.push(path[k]);
                k += 1;
            }
            out.push(p);
            stack_len = stack_len - 1;
        } else {
            let next_i: usize = stack_idx[top];

            if next_i >= graph[u].len() {
                stack_len = stack_len - 1;
            } else {
                let v_i64: i64 = graph[u][next_i];
                stack_idx[top] = next_i + 1;

                let v: usize = v_i64 as usize;
                path[stack_len] = v_i64;
                stack_nodes[stack_len] = v;
                stack_idx[stack_len] = 0;
                stack_len = stack_len + 1;
            }
        }
    }

    out
}
