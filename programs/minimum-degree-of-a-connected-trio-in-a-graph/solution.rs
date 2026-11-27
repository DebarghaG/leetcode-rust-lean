pub fn min_trio_degree(n: i64, edges: &[Vec<i64>]) -> i64 {
    let nn: usize = n as usize;
    if nn < 3 {
        return -1;
    }

    // Degrees of all vertices.
    let mut deg: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < nn {
        deg.push(0);
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let u: usize = (edges[e][0] - 1) as usize;
        let v: usize = (edges[e][1] - 1) as usize;
        deg[u] = deg[u] + 1;
        deg[v] = deg[v] + 1;
        e += 1;
    }

    // Allocate adjacency lists sized by degree (work scales with edges, not n*n).
    let mut adj: Vec<Vec<i64>> = Vec::new();
    i = 0;
    while i < nn {
        let d: usize = deg[i] as usize;
        let mut row: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < d {
            row.push(0);
            k += 1;
        }
        adj.push(row);
        i += 1;
    }

    let mut cnt: Vec<i64> = Vec::new();
    i = 0;
    while i < nn {
        cnt.push(0);
        i += 1;
    }

    // Fill adjacency lists.
    e = 0;
    while e < edges.len() {
        let u: usize = (edges[e][0] - 1) as usize;
        let v: usize = (edges[e][1] - 1) as usize;

        let pu: usize = cnt[u] as usize;
        adj[u][pu] = v as i64;
        cnt[u] = cnt[u] + 1;

        let pv: usize = cnt[v] as usize;
        adj[v][pv] = u as i64;
        cnt[v] = cnt[v] + 1;

        e += 1;
    }

    // Insertion-sort each adjacency list in ascending order.
    i = 0;
    while i < nn {
        let d: usize = adj[i].len();
        let mut a: usize = 1;
        while a < d {
            let key: i64 = adj[i][a];
            let mut b: usize = a;
            while b > 0 {
                let prev: i64 = adj[i][b - 1];
                if prev > key {
                    adj[i][b] = prev;
                    b -= 1;
                } else {
                    break;
                }
            }
            adj[i][b] = key;
            a += 1;
        }
        i += 1;
    }

    // For every vertex u (the smallest of the trio), examine pairs of its
    // neighbours a < b with a > u, and test whether a and b are adjacent.
    let mut best: i64 = -1;
    i = 0;
    while i < nn {
        let u: usize = i;
        let ui: i64 = u as i64;
        let du: usize = adj[u].len();

        let mut ai: usize = 0;
        while ai < du {
            let a: i64 = adj[u][ai];
            if a > ui {
                let au: usize = a as usize;
                let da: usize = adj[au].len();

                let mut bi: usize = ai + 1;
                while bi < du {
                    let b: i64 = adj[u][bi];

                    // Binary search for b in adj[au].
                    let mut lo: usize = 0;
                    let mut hi: usize = da;
                    let mut found: bool = false;
                    while lo < hi {
                        let mid: usize = (lo + hi) / 2;
                        let val: i64 = adj[au][mid];
                        if val == b {
                            found = true;
                            lo = hi;
                        } else if val < b {
                            lo = mid + 1;
                        } else {
                            hi = mid;
                        }
                    }

                    if found {
                        let s: i64 = deg[u] + deg[au] + deg[b as usize] - 6;
                        if best == -1 {
                            best = s;
                        } else {
                            if s < best {
                                best = s;
                            }
                        }
                    }

                    bi += 1;
                }
            }
            ai += 1;
        }

        i += 1;
    }

    best
}
