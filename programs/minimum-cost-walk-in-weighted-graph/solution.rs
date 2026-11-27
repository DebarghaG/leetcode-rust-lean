fn find(parent: &mut Vec<i64>, mut x: usize) -> usize {
    while parent[x] != (x as i64) {
        let p: usize = parent[x] as usize;
        let gp: usize = parent[p] as usize;
        parent[x] = gp as i64;
        x = gp;
    }
    x
}

pub fn minimum_cost(n: i64, edges: &[Vec<i64>], query: &[Vec<i64>]) -> Vec<i64> {
    let nn: usize = n as usize;

    let mut parent: Vec<i64> = Vec::new();
    let mut size: Vec<i64> = Vec::new();
    let mut andv: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < nn {
        parent.push(i as i64);
        size.push(1);
        andv.push(-1);
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let u: usize = edges[e][0] as usize;
        let v: usize = edges[e][1] as usize;
        let w: i64 = edges[e][2];

        let mut ru: usize = find(&mut parent, u);
        let mut rv: usize = find(&mut parent, v);

        if ru == rv {
            andv[ru] = andv[ru] & w;
        } else {
            if size[ru] < size[rv] {
                let tmp: usize = ru;
                ru = rv;
                rv = tmp;
            }

            parent[rv] = ru as i64;
            size[ru] = size[ru] + size[rv];
            andv[ru] = andv[ru] & andv[rv] & w;
        }

        e += 1;
    }

    let mut ans: Vec<i64> = Vec::new();

    let mut qi: usize = 0;
    while qi < query.len() {
        let s: usize = query[qi][0] as usize;
        let t: usize = query[qi][1] as usize;

        let rs: usize = find(&mut parent, s);
        let rt: usize = find(&mut parent, t);

        if rs != rt {
            ans.push(-1);
        } else {
            ans.push(andv[rs]);
        }

        qi += 1;
    }

    ans
}
