fn find(parent: &mut Vec<i64>, mut x: i64) -> i64 {
    let len = parent.len() as i64;
    if x >= len {
        return len - 1;
    }
    if x < 0 {
        x = 0;
    }

    while parent[x as usize] != x {
        let p = parent[x as usize];
        let gp = parent[p as usize];
        parent[x as usize] = gp;
        x = gp;
    }
    x
}

pub fn longest_common_prefix(words: &[Vec<u8>], k: i64) -> Vec<i64> {
    let n = words.len();
    let n_i = n as i64;

    if k > n_i - 1 {
        let mut zero: Vec<i64> = Vec::new();
        let mut i = 0;
        while i < n {
            zero.push(0);
            i += 1;
        }
        return zero;
    }

    // Trie stored in a flat array: node * 26 + character
    let mut child: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < 26 {
        child.push(-1);
        j += 1;
    }

    let mut cnt: Vec<i64> = Vec::new();
    cnt.push(0);

    let mut depth: Vec<i64> = Vec::new();
    depth.push(0);

    let mut max_depth: i64 = 0;

    let mut wi = 0;
    while wi < n {
        let w = &words[wi];
        let mut node: usize = 0;
        let mut pos = 0;

        while pos < w.len() {
            let c = (w[pos] - b'a') as usize;
            let idx = node * 26 + c;
            let mut nxt = child[idx];

            if nxt == -1 {
                let new_id = cnt.len() as i64;
                let nd = depth[node] + 1;

                let mut q = 0;
                while q < 26 {
                    child.push(-1);
                    q += 1;
                }

                cnt.push(0);
                depth.push(nd);
                child[idx] = new_id;
                nxt = new_id;

                if nd > max_depth {
                    max_depth = nd;
                }
            }

            node = nxt as usize;
            cnt[node] += 1;
            pos += 1;
        }

        wi += 1;
    }

    let num_nodes = cnt.len();

    let mut buckets: Vec<Vec<i64>> = Vec::new();
    let mut d = 0;
    while d <= max_depth {
        buckets.push(Vec::new());
        d += 1;
    }

    let mut global_always: i64 = 0;

    let mut u = 1;
    while u < num_nodes {
        let dep = depth[u];
        let c = cnt[u];

        if c == k {
            buckets[dep as usize].push(u as i64);
        }

        if c > k && dep > global_always {
            global_always = dep;
        }

        u += 1;
    }

    let mut occ: Vec<Vec<i64>> = Vec::new();
    u = 0;
    while u < num_nodes {
        occ.push(Vec::new());
        u += 1;
    }

    wi = 0;
    while wi < n {
        let w = &words[wi];
        let mut node: usize = 0;
        let mut pos = 0;

        while pos < w.len() {
            let c = (w[pos] - b'a') as usize;
            let idx = node * 26 + c;
            node = child[idx] as usize;

            if cnt[node] == k {
                occ[node].push(wi as i64);
            }

            pos += 1;
        }

        wi += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        ans.push(global_always);
        i += 1;
    }

    let mut mark: Vec<bool> = Vec::new();
    i = 0;
    while i < n {
        mark.push(false);
        i += 1;
    }

    // DSU "next unassigned index" structure
    let mut parent: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        parent.push(i as i64);
        i += 1;
    }
    parent.push(n_i);

    let mut dcur = max_depth;
    while dcur >= 1 {
        let bucket_len = buckets[dcur as usize].len();
        let mut bi = 0;

        while bi < bucket_len {
            let node = buckets[dcur as usize][bi] as usize;
            let len_here = dcur;

            let occ_len = occ[node].len();
            let mut oi = 0;

            while oi < occ_len {
                let idx = occ[node][oi] as usize;
                mark[idx] = true;
                oi += 1;
            }

            let mut cur = find(&mut parent, 0);

            while cur < n_i {
                let idx = cur as usize;

                if ans[idx] >= len_here {
                    let nxt = find(&mut parent, cur + 1);
                    parent[idx] = nxt;
                    cur = nxt;
                } else if mark[idx] {
                    cur = find(&mut parent, cur + 1);
                } else {
                    ans[idx] = len_here;
                    let nxt = find(&mut parent, cur + 1);
                    parent[idx] = nxt;
                    cur = nxt;
                }
            }

            oi = 0;
            while oi < occ_len {
                let idx = occ[node][oi] as usize;
                mark[idx] = false;
                oi += 1;
            }

            bi += 1;
        }

        dcur -= 1;
    }

    ans
}
