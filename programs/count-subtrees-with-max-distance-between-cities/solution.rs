pub fn count_subgraphs_for_each_diameter(n: i64, edges: &[Vec<i64>]) -> Vec<i64> {
    let n_usize: usize = n as usize;

    let mut ans: Vec<i64> = Vec::new();
    let mut d: i64 = 1;
    while d < n {
        ans.push(0);
        d += 1;
    }

    let mut adj: Vec<i64> = Vec::new();
    let total_cells: usize = n_usize * n_usize;
    let mut idx: usize = 0;
    while idx < total_cells {
        adj.push(0);
        idx += 1;
    }

    let mut i: usize = 0;
    while i < edges.len() {
        let u_i64: i64 = edges[i][0] - 1;
        let v_i64: i64 = edges[i][1] - 1;
        let u: usize = u_i64 as usize;
        let v: usize = v_i64 as usize;
        adj[u * n_usize + v] = 1;
        adj[v * n_usize + u] = 1;
        i += 1;
    }

    let mut total: i64 = 1;
    let mut k: i64 = 0;
    while k < n {
        total = total * 2;
        k += 1;
    }

    let mut mask: i64 = 1;
    while mask < total {
        let mut start: usize = n_usize;
        let mut subset_size: i64 = 0;

        i = 0;
        while i < n_usize {
            let bit: i64 = 1_i64 << (i as i64);
            if (mask & bit) != 0 {
                subset_size += 1;
                if start == n_usize {
                    start = i;
                }
            }
            i += 1;
        }

        if start != n_usize {
            let mut dist: Vec<i64> = Vec::new();
            i = 0;
            while i < n_usize {
                dist.push(-1);
                i += 1;
            }

            let mut queue: Vec<i64> = Vec::new();
            dist[start] = 0;
            queue.push(start as i64);

            let mut head: usize = 0;
            let mut count: i64 = 0;
            let mut far_node: usize = start;
            let mut maxd: i64 = 0;

            while head < queue.len() {
                let u_i64: i64 = queue[head];
                let u: usize = u_i64 as usize;
                head += 1;
                count += 1;

                let du: i64 = dist[u];
                if du > maxd {
                    maxd = du;
                    far_node = u;
                }

                let mut v: usize = 0;
                while v < n_usize {
                    if adj[u * n_usize + v] != 0 {
                        let vbit: i64 = 1_i64 << (v as i64);
                        if (mask & vbit) != 0 && dist[v] == -1 {
                            dist[v] = du + 1;
                            queue.push(v as i64);
                        }
                    }
                    v += 1;
                }
            }

            if count == subset_size {
                let mut dist2: Vec<i64> = Vec::new();
                i = 0;
                while i < n_usize {
                    dist2.push(-1);
                    i += 1;
                }

                let mut queue2: Vec<i64> = Vec::new();
                dist2[far_node] = 0;
                queue2.push(far_node as i64);

                let mut head2: usize = 0;
                let mut diam: i64 = 0;

                while head2 < queue2.len() {
                    let u_i64: i64 = queue2[head2];
                    let u: usize = u_i64 as usize;
                    head2 += 1;

                    let du: i64 = dist2[u];
                    if du > diam {
                        diam = du;
                    }

                    let mut v: usize = 0;
                    while v < n_usize {
                        if adj[u * n_usize + v] != 0 {
                            let vbit: i64 = 1_i64 << (v as i64);
                            if (mask & vbit) != 0 && dist2[v] == -1 {
                                dist2[v] = du + 1;
                                queue2.push(v as i64);
                            }
                        }
                        v += 1;
                    }
                }

                if diam >= 1 {
                    ans[(diam - 1) as usize] += 1;
                }
            }
        }

        mask += 1;
    }

    ans
}
