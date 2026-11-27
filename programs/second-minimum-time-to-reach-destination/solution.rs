pub fn second_minimum(n: i64, edges: &[Vec<i64>], time: i64, change: i64) -> i64 {
    let nv = n as usize;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < nv {
        adj.push(Vec::new());
        i += 1;
    }

    let mut e = 0;
    while e < edges.len() {
        let u = edges[e][0] - 1;
        let v = edges[e][1] - 1;
        let ui = u as usize;
        let vi = v as usize;
        adj[ui].push(v);
        adj[vi].push(u);
        e += 1;
    }

    let inf: i64 = 1000000000;
    let mut d1: Vec<i64> = Vec::new();
    let mut d2: Vec<i64> = Vec::new();

    let mut k = 0;
    while k < nv {
        d1.push(inf);
        d2.push(inf);
        k += 1;
    }

    d1[0] = 0;

    let mut qn: Vec<i64> = Vec::new();
    let mut qd: Vec<i64> = Vec::new();
    qn.push(0);
    qd.push(0);

    let mut head = 0;
    while head < qn.len() {
        let cur = qn[head] as usize;
        let d = qd[head];
        let nd = d + 1;

        let mut j = 0;
        while j < adj[cur].len() {
            let nb = adj[cur][j] as usize;

            if nd < d1[nb] {
                d2[nb] = d1[nb];
                d1[nb] = nd;
                qn.push(nb as i64);
                qd.push(nd);
            } else if nd > d1[nb] && nd < d2[nb] {
                d2[nb] = nd;
                qn.push(nb as i64);
                qd.push(nd);
            }

            j += 1;
        }

        head += 1;
    }

    let steps = d2[nv - 1];
    let cycle = 2 * change;

    let mut t: i64 = 0;
    let mut s = 0;
    while s < steps {
        let rem = t % cycle;
        if rem >= change {
            t += cycle - rem;
        }
        t += time;
        s += 1;
    }

    t
}
