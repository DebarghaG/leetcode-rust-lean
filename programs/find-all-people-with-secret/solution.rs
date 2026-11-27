fn dsu_find(parent: &Vec<i64>, x: i64) -> i64 {
    let mut r = x;
    while parent[r as usize] != r {
        r = parent[r as usize];
    }
    r
}

fn dsu_union(parent: &mut Vec<i64>, rank: &mut Vec<i64>, a: i64, b: i64) {
    let ra = dsu_find(&*parent, a);
    let rb = dsu_find(&*parent, b);
    if ra == rb {
        return;
    }
    if rank[ra as usize] > rank[rb as usize] {
        parent[rb as usize] = ra;
    } else if rank[ra as usize] < rank[rb as usize] {
        parent[ra as usize] = rb;
    } else {
        parent[rb as usize] = ra;
        rank[ra as usize] += 1;
    }
}

pub fn find_all_people(n: i64, meetings: &[Vec<i64>], firstPerson: i64) -> Vec<i64> {
    let n_usize = n as usize;
    let m_usize = meetings.len();

    let mut secret: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        secret.push(false);
        i += 1;
    }
    secret[0] = true;
    if firstPerson >= 0 && firstPerson < n {
        secret[firstPerson as usize] = true;
    }

    let mut parent: Vec<i64> = Vec::new();
    let mut rank: Vec<i64> = Vec::new();
    let mut good: Vec<bool> = Vec::new();

    i = 0;
    while i < n_usize {
        parent.push(i as i64);
        rank.push(0);
        good.push(false);
        i += 1;
    }

    let mut max_t: i64 = 0;
    i = 0;
    while i < m_usize {
        let t = meetings[i][2];
        if t > max_t {
            max_t = t;
        }
        i += 1;
    }

    let mut head: Vec<i64> = Vec::new();
    let mut t: i64 = 0;
    while t <= max_t {
        head.push(-1);
        t += 1;
    }

    let mut next: Vec<i64> = Vec::new();
    i = 0;
    while i < m_usize {
        next.push(-1);
        i += 1;
    }

    i = 0;
    while i < m_usize {
        let tt = meetings[i][2];
        let ti = tt as usize;
        next[i] = head[ti];
        head[ti] = i as i64;
        i += 1;
    }

    t = 0;
    while t <= max_t {
        let ti = t as usize;

        let mut touched: Vec<i64> = Vec::new();

        let mut idx = head[ti];
        while idx != -1 {
            let mi = idx as usize;
            let u = meetings[mi][0];
            let v = meetings[mi][1];

            parent[u as usize] = u;
            rank[u as usize] = 0;
            parent[v as usize] = v;
            rank[v as usize] = 0;

            touched.push(u);
            touched.push(v);

            idx = next[mi];
        }

        idx = head[ti];
        while idx != -1 {
            let mi = idx as usize;
            let u = meetings[mi][0];
            let v = meetings[mi][1];
            dsu_union(&mut parent, &mut rank, u, v);
            idx = next[mi];
        }

        let mut good_roots: Vec<i64> = Vec::new();

        let mut q: usize = 0;
        while q < touched.len() {
            let v = touched[q];
            if secret[v as usize] {
                let r = dsu_find(&parent, v);
                if !good[r as usize] {
                    good[r as usize] = true;
                    good_roots.push(r);
                }
            }
            q += 1;
        }

        q = 0;
        while q < touched.len() {
            let v = touched[q];
            let r = dsu_find(&parent, v);
            if good[r as usize] {
                secret[v as usize] = true;
            }
            q += 1;
        }

        q = 0;
        while q < good_roots.len() {
            let r = good_roots[q];
            good[r as usize] = false;
            q += 1;
        }

        t += 1;
    }

    let mut result: Vec<i64> = Vec::new();
    let mut p: i64 = 0;
    while p < n {
        if secret[p as usize] {
            result.push(p);
        }
        p += 1;
    }

    result
}
