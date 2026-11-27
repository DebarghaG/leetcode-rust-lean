fn to_usize(table: &[i64], x: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = table.len();
    while lo < hi {
        let mid: usize = (lo + hi) / 2;
        if table[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

pub fn longest_special_path(edges: &[Vec<i64>], nums: &[i64]) -> Vec<i64> {
    let n: usize = nums.len();

    let mut id_values: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let mut iv: i64 = 0;
    while i < n {
        id_values.push(iv);
        i += 1;
        iv += 1;
    }

    let mut max_val: i64 = 0;
    i = 0;
    while i < n {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i += 1;
    }

    let mut val_values: Vec<i64> = Vec::new();
    let mut vv: i64 = 0;
    while vv <= max_val {
        val_values.push(vv);
        vv += 1;
    }

    let mut adj_nodes: Vec<Vec<usize>> = Vec::new();
    let mut adj_weights: Vec<Vec<i64>> = Vec::new();
    i = 0;
    while i < n {
        adj_nodes.push(Vec::new());
        adj_weights.push(Vec::new());
        i += 1;
    }

    i = 0;
    while i < edges.len() {
        let u_i = edges[i][0];
        let v_i = edges[i][1];
        let w = edges[i][2];
        let u = to_usize(&id_values, u_i);
        let v = to_usize(&id_values, v_i);

        adj_nodes[u].push(v);
        adj_weights[u].push(w);
        adj_nodes[v].push(u);
        adj_weights[v].push(w);

        i += 1;
    }

    let mut last_stacks: Vec<Vec<usize>> = Vec::new();
    i = 0;
    while i < val_values.len() {
        last_stacks.push(Vec::new());
        i += 1;
    }

    let mut path_dist: Vec<i64> = Vec::new();

    let mut st_event: Vec<bool> = Vec::new();
    let mut st_node: Vec<usize> = Vec::new();
    let mut st_parent: Vec<usize> = Vec::new();
    let mut st_depth: Vec<usize> = Vec::new();
    let mut st_dist: Vec<i64> = Vec::new();
    let mut st_low: Vec<usize> = Vec::new();

    st_event.push(true);
    st_node.push(0);
    st_parent.push(n);
    st_depth.push(0);
    st_dist.push(0);
    st_low.push(0);

    let mut best_len: i64 = -1;
    let mut best_nodes: usize = 0;

    while st_event.len() > 0 {
        let top = st_event.len() - 1;
        let event = st_event[top];
        let node = st_node[top];

        if event {
            let parent = st_parent[top];
            let depth = st_depth[top];
            let cur_dist = st_dist[top];
            let incoming_low = st_low[top];

            st_event.pop();
            st_node.pop();
            st_parent.pop();
            st_depth.pop();
            st_dist.pop();
            st_low.pop();

            let val_idx = to_usize(&val_values, nums[node]);

            let mut cur_low = incoming_low;
            let st_len = last_stacks[val_idx].len();
            if st_len > 0 {
                let old_depth = last_stacks[val_idx][st_len - 1];
                if old_depth + 1 > cur_low {
                    cur_low = old_depth + 1;
                }
            }
            last_stacks[val_idx].push(depth);

            path_dist.push(cur_dist);

            let anc_dist = path_dist[cur_low];
            let cand_len = cur_dist - anc_dist;
            let cand_nodes = depth - cur_low + 1;

            if cand_len > best_len || (cand_len == best_len && cand_nodes < best_nodes) {
                best_len = cand_len;
                best_nodes = cand_nodes;
            }

            st_event.push(false);
            st_node.push(node);
            st_parent.push(0);
            st_depth.push(0);
            st_dist.push(0);
            st_low.push(val_idx);

            let deg = adj_nodes[node].len();
            let mut j: usize = 0;
            while j < deg {
                let to = adj_nodes[node][j];
                let w = adj_weights[node][j];
                if to != parent {
                    st_event.push(true);
                    st_node.push(to);
                    st_parent.push(node);
                    st_depth.push(depth + 1);
                    st_dist.push(cur_dist + w);
                    st_low.push(cur_low);
                }
                j += 1;
            }
        } else {
            let val_idx = st_low[top];

            st_event.pop();
            st_node.pop();
            st_parent.pop();
            st_depth.pop();
            st_dist.pop();
            st_low.pop();

            path_dist.pop();
            last_stacks[val_idx].pop();
        }
    }

    let mut count_values: Vec<i64> = Vec::new();
    let mut ci: usize = 0;
    let mut cv: i64 = 0;
    while ci <= n {
        count_values.push(cv);
        ci += 1;
        cv += 1;
    }

    let mut result: Vec<i64> = Vec::new();
    result.push(best_len);
    result.push(count_values[best_nodes]);
    result
}
