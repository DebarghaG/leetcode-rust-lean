pub fn count_sub_trees(n: i64, edges: &[Vec<i64>], labels: &[u8]) -> Vec<i64> {
    let nn = n as usize;

    let mut head: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < nn {
        head.push(-1);
        i += 1;
    }

    let mut to: Vec<i64> = Vec::new();
    let mut nxt: Vec<i64> = Vec::new();
    let mut eidx: i64 = 0;
    let mut ei: usize = 0;
    while ei < edges.len() {
        let a = edges[ei][0];
        let b = edges[ei][1];

        to.push(b);
        nxt.push(head[a as usize]);
        head[a as usize] = eidx;
        eidx += 1;

        to.push(a);
        nxt.push(head[b as usize]);
        head[b as usize] = eidx;
        eidx += 1;

        ei += 1;
    }

    let mut parent: Vec<i64> = Vec::new();
    i = 0;
    while i < nn {
        parent.push(-1);
        i += 1;
    }

    let mut order: Vec<i64> = Vec::new();
    order.push(0);
    let mut qi: usize = 0;
    while qi < order.len() {
        let u = order[qi];
        qi += 1;

        let mut e = head[u as usize];
        while e != -1 {
            let w = to[e as usize];
            if w != parent[u as usize] {
                parent[w as usize] = u;
                order.push(w);
            }
            e = nxt[e as usize];
        }
    }

    let total = nn * 26;
    let mut cnt: Vec<i64> = Vec::new();
    i = 0;
    while i < total {
        cnt.push(0);
        i += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    i = 0;
    while i < nn {
        ans.push(0);
        i += 1;
    }

    let mut k: usize = order.len();
    while k > 0 {
        k -= 1;
        let v = order[k];
        let vu = v as usize;

        let label_index = (labels[vu] as i64) - 97;
        let own_index = vu * 26 + (label_index as usize);
        cnt[own_index] = cnt[own_index] + 1;
        ans[vu] = cnt[own_index];

        let p = parent[vu];
        if p >= 0 {
            let pu = p as usize;
            let mut c: usize = 0;
            while c < 26 {
                let pi = pu * 26 + c;
                let vi = vu * 26 + c;
                let value = cnt[pi] + cnt[vi];
                cnt[pi] = value;
                c += 1;
            }
        }
    }

    ans
}
