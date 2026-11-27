pub fn maximum_invitations(favorite: &[i64]) -> i64 {
    let n = favorite.len();

    let mut indeg: Vec<i64> = Vec::new();
    let mut depth: Vec<i64> = Vec::new();
    let mut visited: Vec<bool> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        indeg.push(0);
        depth.push(0);
        visited.push(false);
        i += 1;
    }

    i = 0;
    while i < n {
        let v = favorite[i] as usize;
        indeg[v] = indeg[v] + 1;
        i += 1;
    }

    let mut queue: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        if indeg[i] == 0 {
            queue.push(i as i64);
        }
        i += 1;
    }

    let mut head: usize = 0;
    while head < queue.len() {
        let u = queue[head] as usize;
        let v = favorite[u] as usize;

        let candidate = depth[u] + 1;
        if candidate > depth[v] {
            depth[v] = candidate;
        }

        indeg[v] = indeg[v] - 1;
        if indeg[v] == 0 {
            queue.push(v as i64);
        }

        head += 1;
    }

    let mut max_cycle: i64 = 0;
    let mut pair_sum: i64 = 0;

    i = 0;
    while i < n {
        if !visited[i] && indeg[i] > 0 {
            let start = i;
            let mut cur = i;
            let mut len: i64 = 0;

            while !visited[cur] {
                visited[cur] = true;
                len = len + 1;
                cur = favorite[cur] as usize;
            }

            if len == 1 {
                pair_sum = pair_sum + 1 + depth[start];
            } else if len == 2 {
                let other = favorite[start] as usize;
                pair_sum = pair_sum + 2 + depth[start] + depth[other];
            } else {
                if len > max_cycle {
                    max_cycle = len;
                }
            }
        }

        i += 1;
    }

    if pair_sum > max_cycle {
        pair_sum
    } else {
        max_cycle
    }
}
