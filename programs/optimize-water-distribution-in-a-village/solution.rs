pub fn min_cost_to_supply_water(n: i64, wells: &[i64], pipes: &[Vec<i64>]) -> i64 {
    let base: i64 = 100000;
    let base2: i64 = base * base;

    let mut edges: Vec<i64> = Vec::new();
    let mut max_cost: i64 = 0;

    let mut i: i64 = 1;
    while i <= n {
        let cost = wells[(i - 1) as usize];
        let e = cost * base2 + i;
        edges.push(e);
        if cost > max_cost {
            max_cost = cost;
        }
        i += 1;
    }

    let mut j: usize = 0;
    while j < pipes.len() {
        let p = &pipes[j];
        let u = p[0];
        let v = p[1];
        let cost = p[2];
        let e = cost * base2 + u * base + v;
        edges.push(e);
        if cost > max_cost {
            max_cost = cost;
        }
        j += 1;
    }

    // Counting sort by edge cost, using the encoded edge value.
    let m = (max_cost + 1) as usize;
    let mut count: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < m {
        count.push(0);
        k += 1;
    }

    let mut eidx: usize = 0;
    while eidx < edges.len() {
        let e = edges[eidx];
        let c = e / base2;
        count[c as usize] = count[c as usize] + 1;
        eidx += 1;
    }

    let mut sum: i64 = 0;
    let mut idx: usize = 0;
    while idx < m {
        let freq = count[idx];
        count[idx] = sum;
        sum += freq;
        idx += 1;
    }

    let mut sorted: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < edges.len() {
        sorted.push(0);
        z += 1;
    }

    eidx = 0;
    while eidx < edges.len() {
        let e = edges[eidx];
        let c = e / base2;
        let pos = count[c as usize];
        sorted[pos as usize] = e;
        count[c as usize] = pos + 1;
        eidx += 1;
    }

    // Kruskal with a virtual node 0. Houses are nodes 1..=n.
    let nodes = (n + 1) as usize;
    let mut parent: Vec<i64> = Vec::new();
    let mut rank: Vec<i64> = Vec::new();

    let mut t: usize = 0;
    while t < nodes {
        parent.push(t as i64);
        rank.push(0);
        t += 1;
    }

    let mut total: i64 = 0;
    let mut used: i64 = 0;
    let mut pos_i: usize = 0;

    while pos_i < sorted.len() && used < n {
        let e = sorted[pos_i];
        let cost = e / base2;
        let rem = e % base2;
        let u = rem / base;
        let v = rem % base;

        let mut ru = u;
        while parent[ru as usize] != ru {
            ru = parent[ru as usize];
        }

        let mut cur = u;
        while parent[cur as usize] != cur {
            let nxt = parent[cur as usize];
            parent[cur as usize] = ru;
            cur = nxt;
        }

        let mut rv = v;
        while parent[rv as usize] != rv {
            rv = parent[rv as usize];
        }

        let mut curv = v;
        while parent[curv as usize] != curv {
            let nxt = parent[curv as usize];
            parent[curv as usize] = rv;
            curv = nxt;
        }

        if ru != rv {
            let ri = ru as usize;
            let rj = rv as usize;

            if rank[ri] < rank[rj] {
                parent[ri] = rv;
            } else if rank[ri] > rank[rj] {
                parent[rj] = ru;
            } else {
                parent[rj] = ru;
                rank[ri] = rank[ri] + 1;
            }

            total += cost;
            used += 1;
        }

        pos_i += 1;
    }

    total
}
