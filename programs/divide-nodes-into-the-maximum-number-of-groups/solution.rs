pub fn magnificent_sets(n: i64, edges: &[Vec<i64>]) -> i64 {
    let n_usize = n as usize;
    if n_usize == 0 {
        return 0;
    }

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        adj.push(Vec::new());
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let edge = &edges[e];
        let a = edge[0] - 1;
        let b = edge[1] - 1;
        adj[a as usize].push(b);
        adj[b as usize].push(a);
        e += 1;
    }

    let mut color: Vec<i64> = Vec::new();
    i = 0;
    while i < n_usize {
        color.push(-1);
        i += 1;
    }

    let mut answer: i64 = 0;
    let mut start: usize = 0;
    let mut impossible = false;

    while start < n_usize && !impossible {
        if color[start] == -1 {
            let mut comp: Vec<i64> = Vec::new();
            let mut queue: Vec<i64> = Vec::new();

            color[start] = 0;
            comp.push(start as i64);
            queue.push(start as i64);

            let mut head: usize = 0;

            while head < queue.len() && !impossible {
                let u: i64 = queue[head];
                head += 1;

                let row = &adj[u as usize];
                let mut j: usize = 0;

                while j < row.len() && !impossible {
                    let v: i64 = row[j];
                    let vu = v as usize;

                    if color[vu] == -1 {
                        color[vu] = 1 - color[u as usize];
                        comp.push(v);
                        queue.push(v);
                    } else if color[vu] == color[u as usize] {
                        impossible = true;
                    }

                    j += 1;
                }
            }

            if !impossible {
                let mut best: i64 = 0;
                let mut cidx: usize = 0;

                while cidx < comp.len() {
                    let d = bfs_depth(n_usize, &adj, comp[cidx]);
                    if d > best {
                        best = d;
                    }
                    cidx += 1;
                }

                answer += best + 1;
            }
        }

        start += 1;
    }

    if impossible {
        return -1;
    }

    answer
}

fn bfs_depth(n: usize, adj: &[Vec<i64>], start_node: i64) -> i64 {
    let mut dist: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        dist.push(-1);
        i += 1;
    }

    let mut queue: Vec<i64> = Vec::new();
    dist[start_node as usize] = 0;
    queue.push(start_node);

    let mut head: usize = 0;
    let mut max_dist: i64 = 0;

    while head < queue.len() {
        let u: i64 = queue[head];
        head += 1;

        let du: i64 = dist[u as usize];
        if du > max_dist {
            max_dist = du;
        }

        let row = &adj[u as usize];
        let mut j: usize = 0;

        while j < row.len() {
            let v: i64 = row[j];
            let vu = v as usize;

            if dist[vu] == -1 {
                dist[vu] = du + 1;
                queue.push(v);
            }

            j += 1;
        }
    }

    max_dist
}
