pub fn tree_diameter(edges: &[Vec<i64>]) -> i64 {
    let n: usize = edges.len() + 1;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let a_i: i64 = edges[e][0];
        let b_i: i64 = edges[e][1];
        let a: usize = a_i as usize;
        let b: usize = b_i as usize;
        adj[a].push(b_i);
        adj[b].push(a_i);
        e += 1;
    }

    let far: i64 = farthest_node(0, &adj);
    max_distance(far, &adj)
}

fn farthest_node(start: i64, adj: &[Vec<i64>]) -> i64 {
    let n: usize = adj.len();

    let mut dist: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        dist.push(-1);
        i += 1;
    }

    let mut q: Vec<i64> = Vec::new();
    q.push(start);
    dist[start as usize] = 0;

    let mut head: usize = 0;
    let mut far_node: i64 = start;
    let mut far_dist: i64 = 0;

    while head < q.len() {
        let u_i: i64 = q[head];
        head += 1;
        let u: usize = u_i as usize;
        let d: i64 = dist[u];

        if d > far_dist {
            far_dist = d;
            far_node = u_i;
        }

        let row = &adj[u];
        let mut k: usize = 0;
        while k < row.len() {
            let v_i: i64 = row[k];
            let v: usize = v_i as usize;
            if dist[v] < 0 {
                dist[v] = d + 1;
                q.push(v_i);
            }
            k += 1;
        }
    }

    far_node
}

fn max_distance(start: i64, adj: &[Vec<i64>]) -> i64 {
    let n: usize = adj.len();

    let mut dist: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        dist.push(-1);
        i += 1;
    }

    let mut q: Vec<i64> = Vec::new();
    q.push(start);
    dist[start as usize] = 0;

    let mut head: usize = 0;
    let mut far_dist: i64 = 0;

    while head < q.len() {
        let u_i: i64 = q[head];
        head += 1;
        let u: usize = u_i as usize;
        let d: i64 = dist[u];

        if d > far_dist {
            far_dist = d;
        }

        let row = &adj[u];
        let mut k: usize = 0;
        while k < row.len() {
            let v_i: i64 = row[k];
            let v: usize = v_i as usize;
            if dist[v] < 0 {
                dist[v] = d + 1;
                q.push(v_i);
            }
            k += 1;
        }
    }

    far_dist
}
