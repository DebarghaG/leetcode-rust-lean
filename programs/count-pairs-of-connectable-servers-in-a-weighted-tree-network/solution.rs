pub fn count_pairs_of_connectable_servers(edges: &[Vec<i64>], signalSpeed: i64) -> Vec<i64> {
    let n = edges.len() + 1;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < n {
        adj.push(Vec::new());
        i += 1;
    }

    i = 0;
    while i < edges.len() {
        let a = edges[i][0] as usize;
        let b = edges[i][1] as usize;
        let w = edges[i][2];

        adj[a].push(b as i64);
        adj[a].push(w);

        adj[b].push(a as i64);
        adj[b].push(w);

        i += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut c = 0;
    while c < n {
        let deg = adj[c].len() / 2;
        let mut sum: i64 = 0;
        let mut total: i64 = 0;

        let mut k = 0;
        while k < deg {
            let nb_i = adj[c][2 * k];
            let w = adj[c][2 * k + 1];

            let cnt = branch_count(&adj, nb_i as usize, c, w, signalSpeed);
            total += sum * cnt;
            sum += cnt;

            k += 1;
        }

        ans.push(total);
        c += 1;
    }

    ans
}

fn branch_count(
    adj: &[Vec<i64>],
    start: usize,
    parent_start: usize,
    start_dist: i64,
    signalSpeed: i64,
) -> i64 {
    let mut st_node: Vec<i64> = Vec::new();
    let mut st_parent: Vec<i64> = Vec::new();
    let mut st_dist: Vec<i64> = Vec::new();

    st_node.push(start as i64);
    st_parent.push(parent_start as i64);
    st_dist.push(start_dist);

    let mut cnt: i64 = 0;

    while st_node.len() > 0 {
        let last = st_node.len() - 1;
        let node_i = st_node[last];
        let parent_i = st_parent[last];
        let dist = st_dist[last];

        st_node.pop();
        st_parent.pop();
        st_dist.pop();

        if dist % signalSpeed == 0 {
            cnt += 1;
        }

        let node = node_i as usize;
        let parent = parent_i as usize;
        let pairs = adj[node].len() / 2;

        let mut j = 0;
        while j < pairs {
            let nei_i = adj[node][2 * j];
            let w = adj[node][2 * j + 1];
            let nei = nei_i as usize;

            if nei != parent {
                st_node.push(nei_i);
                st_parent.push(node_i);
                st_dist.push(dist + w);
            }

            j += 1;
        }
    }

    cnt
}
