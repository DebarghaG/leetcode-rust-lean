pub fn longest_special_path(edges: &[Vec<i64>], nums: &[i64]) -> Vec<i64> {
    let n = nums.len();

    // Build adjacency as flattened rows: [neighbor, weight, neighbor, weight, ...]
    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    i = 0;
    while i < edges.len() {
        let u = edges[i][0] as usize;
        let v = edges[i][1] as usize;
        let w = edges[i][2];

        adj[u].push(v as i64);
        adj[u].push(w);

        adj[v].push(u as i64);
        adj[v].push(w);

        i += 1;
    }

    let mut max_val: i64 = 0;
    i = 0;
    while i < n {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i += 1;
    }

    let value_count = (max_val + 1) as usize;

    let mut seg_n: usize = 1;
    while seg_n < value_count {
        seg_n *= 2;
    }
    let seg_total = seg_n * 2;

    // For each value, the last three occurrence depths on the current root path.
    let mut pos1: Vec<i64> = Vec::new();
    let mut pos2: Vec<i64> = Vec::new();
    let mut pos3: Vec<i64> = Vec::new();

    i = 0;
    while i < value_count {
        pos1.push(-1);
        pos2.push(-1);
        pos3.push(-1);
        i += 1;
    }

    // Segment tree over values.
    // max3: maximum third-last occurrence depth.
    // max21/max22: largest and second-largest second-last occurrence depths.
    let mut max3: Vec<i64> = Vec::new();
    let mut max21: Vec<i64> = Vec::new();
    let mut max22: Vec<i64> = Vec::new();

    i = 0;
    while i < seg_total {
        max3.push(-1);
        max21.push(-1);
        max22.push(-1);
        i += 1;
    }

    let mut depth_dist: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        depth_dist.push(0);
        i += 1;
    }

    // Explicit DFS stack.
    let mut st_state: Vec<i64> = Vec::new(); // 0 = enter, 1 = exit
    let mut st_u: Vec<i64> = Vec::new();
    let mut st_parent: Vec<i64> = Vec::new();
    let mut st_depth: Vec<i64> = Vec::new();
    let mut st_dist: Vec<i64> = Vec::new();
    let mut st_old1: Vec<i64> = Vec::new();
    let mut st_old2: Vec<i64> = Vec::new();
    let mut st_old3: Vec<i64> = Vec::new();

    st_state.push(0);
    st_u.push(0);
    st_parent.push(-1);
    st_depth.push(0);
    st_dist.push(0);
    st_old1.push(-1);
    st_old2.push(-1);
    st_old3.push(-1);

    let mut ans_len: i64 = -1;
    let mut ans_nodes: i64 = 0;

    while st_state.len() > 0 {
        let top = st_state.len() - 1;

        let state = st_state[top];
        let u_i = st_u[top];
        let parent_i = st_parent[top];
        let depth = st_depth[top];
        let dist = st_dist[top];
        let old1 = st_old1[top];
        let old2 = st_old2[top];
        let old3 = st_old3[top];

        let _ = st_state.pop();
        let _ = st_u.pop();
        let _ = st_parent.pop();
        let _ = st_depth.pop();
        let _ = st_dist.pop();
        let _ = st_old1.pop();
        let _ = st_old2.pop();
        let _ = st_old3.pop();

        if state == 0 {
            let u = u_i as usize;
            let x = nums[u];
            let xi = x as usize;

            let b1 = pos1[xi];
            let b2 = pos2[xi];
            let b3 = pos3[xi];

            pos1[xi] = depth;
            pos2[xi] = b1;
            pos3[xi] = b2;

            let mut idx = seg_n + xi;
            max3[idx] = b2;
            max21[idx] = b1;
            max22[idx] = -1;

            idx = idx / 2;
            while idx > 0 {
                let left = idx * 2;
                let right = left + 1;

                let a3 = max3[left];
                let c3 = max3[right];
                let mut best3 = a3;
                if c3 > best3 {
                    best3 = c3;
                }
                max3[idx] = best3;

                let a1 = max21[left];
                let a2 = max22[left];
                let c1 = max21[right];
                let c2 = max22[right];

                let mut top1 = -1;
                let mut top2 = -1;

                if a1 >= c1 {
                    top1 = a1;
                    top2 = a2;
                    if c1 > top2 {
                        top2 = c1;
                    }
                } else {
                    top1 = c1;
                    top2 = c2;
                    if a1 > top2 {
                        top2 = a1;
                    }
                }

                max21[idx] = top1;
                max22[idx] = top2;

                idx = idx / 2;
            }

            let mut start_d: i64 = 0;

            let t3 = max3[1] + 1;
            if t3 > start_d {
                start_d = t3;
            }

            let t2 = max22[1] + 1;
            if t2 > start_d {
                start_d = t2;
            }

            if start_d < 0 {
                start_d = 0;
            }
            if start_d > depth {
                start_d = depth;
            }

            depth_dist[depth as usize] = dist;
            let start = start_d as usize;

            let path_len = dist - depth_dist[start];
            let nodes = depth - start_d + 1;

            if path_len > ans_len {
                ans_len = path_len;
                ans_nodes = nodes;
            } else {
                if path_len == ans_len {
                    if ans_nodes == 0 || nodes < ans_nodes {
                        ans_nodes = nodes;
                    }
                }
            }

            st_state.push(1);
            st_u.push(u_i);
            st_parent.push(parent_i);
            st_depth.push(depth);
            st_dist.push(dist);
            st_old1.push(b1);
            st_old2.push(b2);
            st_old3.push(b3);

            let row_len = adj[u].len();
            let mut k: usize = 0;
            while k < row_len {
                let v_i = adj[u][k];
                let w = adj[u][k + 1];

                if v_i != parent_i {
                    st_state.push(0);
                    st_u.push(v_i);
                    st_parent.push(u_i);
                    st_depth.push(depth + 1);
                    st_dist.push(dist + w);
                    st_old1.push(-1);
                    st_old2.push(-1);
                    st_old3.push(-1);
                }

                k += 2;
            }
        } else {
            let u = u_i as usize;
            let x = nums[u];
            let xi = x as usize;

            pos1[xi] = old1;
            pos2[xi] = old2;
            pos3[xi] = old3;

            let mut idx = seg_n + xi;
            max3[idx] = old3;
            max21[idx] = old2;
            max22[idx] = -1;

            idx = idx / 2;
            while idx > 0 {
                let left = idx * 2;
                let right = left + 1;

                let a3 = max3[left];
                let c3 = max3[right];
                let mut best3 = a3;
                if c3 > best3 {
                    best3 = c3;
                }
                max3[idx] = best3;

                let a1 = max21[left];
                let a2 = max22[left];
                let c1 = max21[right];
                let c2 = max22[right];

                let mut top1 = -1;
                let mut top2 = -1;

                if a1 >= c1 {
                    top1 = a1;
                    top2 = a2;
                    if c1 > top2 {
                        top2 = c1;
                    }
                } else {
                    top1 = c1;
                    top2 = c2;
                    if a1 > top2 {
                        top2 = a1;
                    }
                }

                max21[idx] = top1;
                max22[idx] = top2;

                idx = idx / 2;
            }
        }
    }

    let mut result: Vec<i64> = Vec::new();
    result.push(ans_len);
    result.push(ans_nodes);
    result
}
