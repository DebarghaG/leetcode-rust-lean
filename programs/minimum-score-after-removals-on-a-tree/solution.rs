pub fn minimum_score(nums: &[i64], edges: &[Vec<i64>]) -> i64 {
    let n = nums.len();

    // Build adjacency list.
    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < n {
        adj.push(Vec::new());
        i += 1;
    }

    let mut e = 0;
    while e < edges.len() {
        let edge = &edges[e];
        let a = edge[0];
        let b = edge[1];
        let ai = a as usize;
        let bi = b as usize;
        adj[ai].push(b);
        adj[bi].push(a);
        e += 1;
    }

    // Arrays for rooted tree information.
    let mut parent: Vec<i64> = Vec::new();
    let mut sub: Vec<i64> = Vec::new();
    let mut tin: Vec<i64> = Vec::new();
    let mut sz: Vec<i64> = Vec::new();

    let mut k = 0;
    while k < n {
        parent.push(-1);
        sub.push(nums[k]);
        tin.push(0);
        sz.push(1);
        k += 1;
    }

    // Iterative DFS from root 0 to build a preorder traversal.
    let mut order: Vec<i64> = Vec::new();
    let mut stack: Vec<i64> = Vec::new();
    stack.push(0);
    let mut sp: usize = 1;

    while sp > 0 {
        sp -= 1;
        let u = stack[sp];
        order.push(u);

        let ui = u as usize;
        let mut j = 0;
        while j < adj[ui].len() {
            let v = adj[ui][j];
            if v != parent[ui] {
                let vi = v as usize;
                parent[vi] = u;

                if sp < stack.len() {
                    stack[sp] = v;
                } else {
                    stack.push(v);
                }
                sp += 1;
            }
            j += 1;
        }
    }

    // Entry times of preorder traversal.
    let mut idx = 0;
    while idx < order.len() {
        let u = order[idx];
        tin[u as usize] = idx as i64;
        idx += 1;
    }

    // Compute subtree XORs and subtree sizes bottom-up.
    let mut idx2 = n;
    while idx2 > 0 {
        idx2 -= 1;
        let u = order[idx2];
        let ui = u as usize;
        let p = parent[ui];
        if p != -1 {
            let pi = p as usize;
            sub[pi] = sub[pi] ^ sub[ui];
            sz[pi] = sz[pi] + sz[ui];
        }
    }

    let total = sub[0];
    let mut ans: i64 = 1000000000000;

    // Every non-root node corresponds to the edge from its parent to it.
    let mut a = 0;
    while a < n {
        if parent[a] != -1 {
            let mut b = a + 1;
            while b < n {
                if parent[b] != -1 {
                    let xa = sub[a];
                    let xb = sub[b];

                    let ta = tin[a];
                    let tb = tin[b];
                    let sa = sz[a];
                    let sb = sz[b];

                    let a_anc_b = ta <= tb && tb < ta + sa;
                    let b_anc_a = tb <= ta && ta < tb + sb;

                    let mut c0 = xa;
                    let mut c1 = xb;
                    let mut c2 = total ^ xa ^ xb;

                    if a_anc_b {
                        c0 = xb;
                        c1 = xa ^ xb;
                        c2 = total ^ xa;
                    } else if b_anc_a {
                        c0 = xa;
                        c1 = xb ^ xa;
                        c2 = total ^ xb;
                    }

                    let mut mx = c0;
                    if c1 > mx {
                        mx = c1;
                    }
                    if c2 > mx {
                        mx = c2;
                    }

                    let mut mn = c0;
                    if c1 < mn {
                        mn = c1;
                    }
                    if c2 < mn {
                        mn = c2;
                    }

                    let score = mx - mn;
                    if score < ans {
                        ans = score;
                    }
                }
                b += 1;
            }
        }
        a += 1;
    }

    ans
}
