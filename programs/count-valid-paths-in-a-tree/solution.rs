pub fn count_paths(n: i64, edges: &[Vec<i64>]) -> i64 {
    let n_usize = n as usize;

    // Sieve of Eratosthenes: is_prime[i] == true iff i is prime.
    let mut is_prime: Vec<bool> = Vec::new();
    let mut i = 0usize;
    while i <= n_usize {
        is_prime.push(true);
        i += 1;
    }

    if n_usize >= 0 {
        is_prime[0] = false;
    }
    if n_usize >= 1 {
        is_prime[1] = false;
    }

    let mut p = 2usize;
    while p <= n_usize {
        if is_prime[p] {
            let mut m = p * p;
            while m <= n_usize {
                is_prime[m] = false;
                m += p;
            }
        }
        p += 1;
    }

    // Build adjacency list. Nodes are 1-indexed.
    let mut adj: Vec<Vec<i64>> = Vec::new();
    i = 0usize;
    while i <= n_usize {
        adj.push(Vec::new());
        i += 1;
    }

    i = 0usize;
    while i < edges.len() {
        let u = edges[i][0];
        let v = edges[i][1];
        let uu = u as usize;
        let vv = v as usize;
        adj[uu].push(v);
        adj[vv].push(u);
        i += 1;
    }

    // comp_id[v] is the id of the non-prime connected component containing v.
    let mut comp_id: Vec<i64> = Vec::new();
    i = 0usize;
    while i <= n_usize {
        comp_id.push(-1);
        i += 1;
    }

    let mut comp_sizes: Vec<i64> = Vec::new();
    let mut visited: Vec<bool> = Vec::new();
    i = 0usize;
    while i <= n_usize {
        visited.push(false);
        i += 1;
    }

    // Find all connected components formed only by non-prime nodes.
    let mut start = 1usize;
    while start <= n_usize {
        if !is_prime[start] && !visited[start] {
            let cid = comp_sizes.len() as i64;
            let mut size: i64 = 0;
            let mut stack: Vec<i64> = Vec::new();

            visited[start] = true;
            stack.push(start as i64);

            while !stack.is_empty() {
                let idx = stack.len() - 1;
                let v = stack[idx];
                stack.pop();

                let vu = v as usize;
                comp_id[vu] = cid;
                size += 1;

                let deg = adj[vu].len();
                let mut k = 0usize;
                while k < deg {
                    let w = adj[vu][k];
                    let wu = w as usize;
                    if !is_prime[wu] && !visited[wu] {
                        visited[wu] = true;
                        stack.push(w);
                    }
                    k += 1;
                }
            }

            comp_sizes.push(size);
        }
        start += 1;
    }

    let mut ans: i64 = 0;

    // For each prime node, combine the non-prime components attached to it.
    let mut prime_node = 1usize;
    while prime_node <= n_usize {
        if is_prime[prime_node] {
            let mut prev_sum: i64 = 0;
            let deg = adj[prime_node].len();
            let mut k = 0usize;

            while k < deg {
                let w = adj[prime_node][k];
                let wu = w as usize;

                if !is_prime[wu] {
                    let cid = comp_id[wu] as usize;
                    let s = comp_sizes[cid];

                    // Paths from this prime node to nodes in this component.
                    ans += s;

                    // Paths between this component and previously seen components,
                    // with this prime node as the unique prime on the path.
                    ans += prev_sum * s;

                    prev_sum += s;
                }

                k += 1;
            }
        }
        prime_node += 1;
    }

    ans
}
