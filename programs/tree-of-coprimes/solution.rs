fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    if a < 0 {
        -a
    } else {
        a
    }
}

pub fn get_coprimes(nums: &[i64], edges: &[Vec<i64>]) -> Vec<i64> {
    let n = nums.len();

    let mut ans: Vec<i64> = Vec::new();
    let mut depth: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        ans.push(-1);
        depth.push(0);
        i += 1;
    }

    if n == 0 {
        return ans;
    }

    let mut adj: Vec<Vec<i64>> = Vec::new();
    i = 0usize;
    while i < n {
        adj.push(Vec::new());
        i += 1;
    }

    let m = edges.len();
    let mut e = 0usize;
    while e < m {
        let u = edges[e][0] as usize;
        let v = edges[e][1] as usize;
        adj[u].push(v as i64);
        adj[v].push(u as i64);
        e += 1;
    }

    // pos[v] = deepest node on the current path whose value equals v.
    // Only values in 1..=50 are tracked (the reference's bounded table).
    let mut pos: Vec<i64> = Vec::new();
    i = 0usize;
    while i < 51 {
        pos.push(-1);
        i += 1;
    }

    let mut st_node: Vec<i64> = Vec::new();
    let mut st_parent: Vec<i64> = Vec::new();
    let mut st_next: Vec<i64> = Vec::new();
    let mut st_key: Vec<i64> = Vec::new(); // pos slot changed by this frame, or -1
    let mut st_old: Vec<i64> = Vec::new(); // previous value of that slot

    // Root (node 0). Only trackable if its value is within 1..=50.
    let mut rk: i64 = -1;
    let mut ro: i64 = -1;
    if nums[0] <= 50 {
        rk = nums[0];
        ro = pos[nums[0] as usize];
        pos[nums[0] as usize] = 0;
    }
    st_node.push(0);
    st_parent.push(-1);
    st_next.push(0);
    st_key.push(rk);
    st_old.push(ro);
    depth[0] = 0;

    while !st_node.is_empty() {
        let top = st_node.len() - 1;
        let node = st_node[top] as usize;
        let alen = adj[node].len() as i64;

        if st_next[top] >= alen {
            let key = st_key[top];
            if key >= 0 {
                pos[key as usize] = st_old[top];
            }
            st_node.pop();
            st_parent.pop();
            st_next.pop();
            st_key.pop();
            st_old.pop();
        } else {
            let idx = st_next[top] as usize;
            let nbr = adj[node][idx];
            st_next[top] = st_next[top] + 1;

            if nbr != st_parent[top] {
                let child = nbr as usize;
                depth[child] = depth[node] + 1;
                let cval = nums[child];

                // Query only values in 1..=50, like the reference table.
                let mut best = -1i64;
                let mut best_depth = -1i64;
                let mut v = 1i64;
                while v <= 50 {
                    let cand = pos[v as usize];
                    if cand >= 0 && gcd(cval, v) == 1 {
                        let cd = depth[cand as usize];
                        if cd > best_depth {
                            best_depth = cd;
                            best = cand;
                        }
                    }
                    v += 1;
                }

                // The reference cannot handle values > 50: leave -1 for them.
                if cval > 50 {
                    ans[child] = -1;
                } else {
                    ans[child] = best;
                }

                // Record this child on the path only if its value is 1..=50.
                let mut ck: i64 = -1;
                let mut co: i64 = -1;
                if cval <= 50 {
                    ck = cval;
                    co = pos[cval as usize];
                    pos[cval as usize] = nbr;
                }

                st_node.push(nbr);
                st_parent.push(node as i64);
                st_next.push(0);
                st_key.push(ck);
                st_old.push(co);
            }
        }
    }

    ans
}
