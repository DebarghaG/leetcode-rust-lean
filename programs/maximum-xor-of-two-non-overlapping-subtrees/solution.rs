pub fn max_xor(n: i64, edges: &[Vec<i64>], values: &[i64]) -> i64 {
    if n < 2 {
        return 0;
    }

    let n_usize = values.len();
    if n_usize < 2 {
        return 0;
    }

    // Build adjacency list.
    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        adj.push(Vec::new());
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let a = edges[e][0];
        let b = edges[e][1];
        adj[a as usize].push(b);
        adj[b as usize].push(a);
        e += 1;
    }

    // Iterative DFS to obtain a valid preorder.
    let mut parent: Vec<i64> = Vec::new();
    i = 0;
    while i < n_usize {
        parent.push(-2);
        i += 1;
    }
    parent[0] = -1;

    let mut order: Vec<i64> = Vec::new();
    let mut stack: Vec<i64> = Vec::new();
    stack.push(0);

    while stack.len() > 0 {
        let last = stack.len() - 1;
        let u = stack[last];
        stack.pop();
        order.push(u);

        let uu = u as usize;
        let mut j: usize = 0;
        while j < adj[uu].len() {
            let v = adj[uu][j];
            let vv = v as usize;
            if parent[vv] == -2 {
                parent[vv] = u;
                stack.push(v);
            }
            j += 1;
        }
    }

    // Subtree sums and sizes.
    let mut sums: Vec<i64> = Vec::new();
    i = 0;
    while i < n_usize {
        sums.push(values[i]);
        i += 1;
    }

    let mut sizes: Vec<i64> = Vec::new();
    i = 0;
    while i < n_usize {
        sizes.push(1);
        i += 1;
    }

    let mut idx = n_usize;
    while idx > 0 {
        idx -= 1;
        let u = order[idx];
        let uu = u as usize;
        let p = parent[uu];
        if p >= 0 {
            let pp = p as usize;
            sums[pp] = sums[pp] + sums[uu];
            sizes[pp] = sizes[pp] + sizes[uu];
        }
    }

    // Linked-list buckets by subtree end position.
    let mut head: Vec<i64> = Vec::new();
    let mut next_node: Vec<i64> = Vec::new();
    i = 0;
    while i < n_usize {
        head.push(-1);
        next_node.push(-1);
        i += 1;
    }

    i = 0;
    while i < n_usize {
        let u = order[i];
        let sz = sizes[u as usize] as usize;
        let tout = i + sz - 1;
        next_node[u as usize] = head[tout];
        head[tout] = u;
        i += 1;
    }

    // Binary trie over completed subtree sums.
    let mut left: Vec<i64> = Vec::new();
    let mut right: Vec<i64> = Vec::new();
    left.push(-1);
    right.push(-1);

    let mut next_index: i64 = 1;
    let mut has_inserted: bool = false;
    let mut ans: i64 = 0;
    let mut pos: usize = 0;

    while pos < n_usize {
        if pos > 0 {
            let mut node_val = head[pos - 1];
            while node_val != -1 {
                let x = sums[node_val as usize];

                let mut node: i64 = 0;
                let mut b: i64 = 60;
                while b >= 0 {
                    let bit = (x >> b) & 1;
                    if bit == 0 {
                        let child = left[node as usize];
                        if child == -1 {
                            let new_idx = next_index;
                            next_index += 1;
                            left.push(-1);
                            right.push(-1);
                            left[node as usize] = new_idx;
                            node = new_idx;
                        } else {
                            node = child;
                        }
                    } else {
                        let child = right[node as usize];
                        if child == -1 {
                            let new_idx = next_index;
                            next_index += 1;
                            left.push(-1);
                            right.push(-1);
                            right[node as usize] = new_idx;
                            node = new_idx;
                        } else {
                            node = child;
                        }
                    }
                    b -= 1;
                }

                has_inserted = true;
                node_val = next_node[node_val as usize];
            }
        }

        if has_inserted {
            let u = order[pos];
            let x = sums[u as usize];

            let mut node: i64 = 0;
            let mut cur: i64 = 0;
            let mut b: i64 = 60;
            while b >= 0 {
                let bit = (x >> b) & 1;
                if bit == 0 {
                    let child = right[node as usize];
                    if child != -1 {
                        cur = cur + (1i64 << b);
                        node = child;
                    } else {
                        node = left[node as usize];
                    }
                } else {
                    let child = left[node as usize];
                    if child != -1 {
                        cur = cur + (1i64 << b);
                        node = child;
                    } else {
                        node = right[node as usize];
                    }
                }
                b -= 1;
            }

            if cur > ans {
                ans = cur;
            }
        }

        pos += 1;
    }

    ans
}
