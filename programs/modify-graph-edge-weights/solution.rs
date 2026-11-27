fn dijkstra(adj: &[i64], n: usize, src: usize) -> Vec<i64> {
    let inf: i64 = 1_000_000_000_000_000_000;
    let mut dist: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        dist.push(inf);
        i += 1;
    }
    dist[src] = 0;

    let mut visited: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        visited.push(0);
        i += 1;
    }

    let mut step: usize = 0;
    while step < n {
        let mut u: i64 = -1;
        let mut best: i64 = inf;
        let mut j: usize = 0;
        while j < n {
            if visited[j] == 0 && dist[j] < best {
                best = dist[j];
                u = j as i64;
            }
            j += 1;
        }

        if u == -1 {
            break;
        }

        let uu: usize = u as usize;
        visited[uu] = 1;

        let mut v: usize = 0;
        while v < n {
            let w: i64 = adj[uu * n + v];
            if w < inf {
                let nd: i64 = dist[uu] + w;
                if nd < dist[v] {
                    dist[v] = nd;
                }
            }
            v += 1;
        }

        step += 1;
    }

    dist
}

fn build_output(edges: &[Vec<i64>], weights: &[i64]) -> Vec<Vec<i64>> {
    let mut out: Vec<Vec<i64>> = Vec::new();
    let m: usize = edges.len();
    let mut i: usize = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        row.push(edges[i][0]);
        row.push(edges[i][1]);
        row.push(weights[i]);
        out.push(row);
        i += 1;
    }
    out
}

pub fn modified_graph_edges(
    n: i64,
    edges: &[Vec<i64>],
    source: i64,
    destination: i64,
    target: i64,
) -> Vec<Vec<i64>> {
    let inf: i64 = 1_000_000_000_000_000_000;
    let large: i64 = 2_000_000_000;

    let n_usize: usize = n as usize;
    let m: usize = edges.len();
    let src: usize = source as usize;
    let dst: usize = destination as usize;

    let mut adj: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        let mut j: usize = 0;
        while j < n_usize {
            adj.push(inf);
            j += 1;
        }
        i += 1;
    }

    let mut weights: Vec<i64> = Vec::new();
    i = 0;
    while i < m {
        let w: i64 = edges[i][2];
        weights.push(w);
        if w != -1 {
            let u: usize = edges[i][0] as usize;
            let v: usize = edges[i][1] as usize;
            adj[u * n_usize + v] = w;
            adj[v * n_usize + u] = w;
        }
        i += 1;
    }

    let dist_pos: Vec<i64> = dijkstra(&adj[..], n_usize, src);
    let d_pos: i64 = dist_pos[dst];

    if d_pos < target {
        return Vec::new();
    }

    if d_pos == target {
        i = 0;
        while i < m {
            if weights[i] == -1 {
                weights[i] = large;
            }
            i += 1;
        }
        return build_output(edges, &weights[..]);
    }

    // d_pos > target
    i = 0;
    while i < m {
        if weights[i] == -1 {
            let u: usize = edges[i][0] as usize;
            let v: usize = edges[i][1] as usize;

            let d0: Vec<i64> = dijkstra(&adj[..], n_usize, src);
            let d1: Vec<i64> = dijkstra(&adj[..], n_usize, dst);

            let prev: i64 = d0[dst];

            let mut a: i64 = inf;
            if d0[u] < inf && d1[v] < inf {
                a = d0[u] + 1 + d1[v];
            }

            let mut b: i64 = inf;
            if d0[v] < inf && d1[u] < inf {
                b = d0[v] + 1 + d1[u];
            }

            let mut new_dist: i64 = prev;
            if a < new_dist {
                new_dist = a;
            }
            if b < new_dist {
                new_dist = b;
            }

            if new_dist <= target {
                let mut min_ab: i64 = inf;

                if d0[u] < inf && d1[v] < inf {
                    let val: i64 = d0[u] + d1[v];
                    if val < min_ab {
                        min_ab = val;
                    }
                }

                if d0[v] < inf && d1[u] < inf {
                    let val: i64 = d0[v] + d1[u];
                    if val < min_ab {
                        min_ab = val;
                    }
                }

                let mut w: i64 = target - min_ab;
                if w < 1 {
                    w = 1;
                }
                if w > large {
                    w = large;
                }

                weights[i] = w;

                let mut j: usize = i + 1;
                while j < m {
                    if weights[j] == -1 {
                        weights[j] = large;
                    }
                    j += 1;
                }

                return build_output(edges, &weights[..]);
            } else {
                weights[i] = 1;
                adj[u * n_usize + v] = 1;
                adj[v * n_usize + u] = 1;
            }
        }

        i += 1;
    }

    Vec::new()
}
