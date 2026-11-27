fn find(parent: &mut Vec<i64>, x: i64) -> i64 {
    let mut cur = x;
    while parent[cur as usize] != cur {
        let p = parent[cur as usize];
        let gp = parent[p as usize];
        parent[cur as usize] = gp;
        cur = gp;
    }
    cur
}

fn union(parent: &mut Vec<i64>, size: &mut Vec<i64>, a: i64, b: i64) -> i64 {
    let ra = find(parent, a);
    let rb = find(parent, b);

    if ra == rb {
        return ra;
    }

    let sa = size[ra as usize];
    let sb = size[rb as usize];

    if sa < sb {
        parent[ra as usize] = rb;
        size[rb as usize] = sa + sb;
        rb
    } else {
        parent[rb as usize] = ra;
        size[ra as usize] = sa + sb;
        ra
    }
}

pub fn are_connected(n: i64, threshold: i64, queries: &[Vec<i64>]) -> Vec<bool> {
    let nn = n as usize;

    let mut parent: Vec<i64> = Vec::new();
    let mut size: Vec<i64> = Vec::new();
    let mut first: Vec<i64> = Vec::new();

    let mut i: i64 = 0;
    while i <= n {
        parent.push(i);
        size.push(1);
        first.push(0);
        i += 1;
    }

    let half = n / 2;
    let mut d = threshold + 1;

    while d <= half {
        // If d is already a multiple of some earlier usable divisor,
        // then d is not a minimal seed and adds no new connections.
        if first[d as usize] == 0 {
            let mut m = d;
            while m <= n {
                let idx = m as usize;
                if first[idx] == 0 {
                    first[idx] = d;
                } else {
                    let e = first[idx];
                    let r = union(&mut parent, &mut size, d, e);
                    first[idx] = r;
                }
                m += d;
            }
        }
        d += 1;
    }

    // Replace each active vertex's representative by its final DSU root.
    let mut v: usize = 1;
    while v <= nn {
        let x = first[v];
        if x != 0 {
            first[v] = find(&mut parent, x);
        }
        v += 1;
    }

    let mut answer: Vec<bool> = Vec::new();
    let mut qi: usize = 0;
    while qi < queries.len() {
        let a = queries[qi][0];
        let b = queries[qi][1];

        if a == b {
            answer.push(true);
        } else {
            let ca = first[a as usize];
            let cb = first[b as usize];
            answer.push(ca != 0 && ca == cb);
        }

        qi += 1;
    }

    answer
}
