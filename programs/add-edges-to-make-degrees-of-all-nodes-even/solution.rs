fn edge_exists(edges: &[Vec<i64>], u: i64, v: i64) -> bool {
    let mut i: usize = 0;
    while i < edges.len() {
        let a = edges[i][0];
        let b = edges[i][1];
        if (a == u && b == v) || (a == v && b == u) {
            return true;
        }
        i += 1;
    }
    false
}

pub fn is_possible(n: i64, edges: &[Vec<i64>]) -> bool {
    let n_us = n as usize;

    let mut deg: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= n_us {
        deg.push(0);
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let a = edges[e][0] as usize;
        let b = edges[e][1] as usize;
        deg[a] += 1;
        deg[b] += 1;
        e += 1;
    }

    let mut odds: Vec<i64> = Vec::new();
    let mut v: usize = 1;
    while v <= n_us {
        if deg[v] % 2 == 1 {
            odds.push(v as i64);
        }
        v += 1;
    }

    let k = odds.len();

    if k == 0 {
        return true;
    }

    if k == 2 {
        let a = odds[0];
        let b = odds[1];
        let a_i = a as usize;
        let b_i = b as usize;

        if !edge_exists(edges, a, b) {
            return true;
        }

        let mut na: Vec<bool> = Vec::new();
        let mut nb: Vec<bool> = Vec::new();
        let mut j: usize = 0;
        while j <= n_us {
            na.push(false);
            nb.push(false);
            j += 1;
        }

        let mut idx: usize = 0;
        while idx < edges.len() {
            let u = edges[idx][0] as usize;
            let w = edges[idx][1] as usize;

            if u == a_i {
                na[w] = true;
            }
            if w == a_i {
                na[u] = true;
            }
            if u == b_i {
                nb[w] = true;
            }
            if w == b_i {
                nb[u] = true;
            }

            idx += 1;
        }

        let mut c: usize = 1;
        while c <= n_us {
            if c != a_i && c != b_i {
                if !na[c] && !nb[c] {
                    return true;
                }
            }
            c += 1;
        }

        return false;
    }

    if k == 4 {
        let a = odds[0];
        let b = odds[1];
        let c = odds[2];
        let d = odds[3];

        let ab = edge_exists(edges, a, b);
        let cd = edge_exists(edges, c, d);
        let ac = edge_exists(edges, a, c);
        let bd = edge_exists(edges, b, d);
        let ad = edge_exists(edges, a, d);
        let bc = edge_exists(edges, b, c);

        if !ab && !cd {
            return true;
        }
        if !ac && !bd {
            return true;
        }
        if !ad && !bc {
            return true;
        }

        return false;
    }

    false
}
