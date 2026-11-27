pub fn find_redundant_connection(edges: &[Vec<i64>]) -> Vec<i64> {
    let n = edges.len();

    let mut parent: Vec<i64> = Vec::new();
    let mut size: Vec<i64> = Vec::new();

    let mut i = 0usize;
    while i <= n {
        parent.push(i as i64);
        size.push(1);
        i += 1;
    }

    let mut idx = 0usize;
    while idx < n {
        let a = edges[idx][0];
        let b = edges[idx][1];

        let mut ra = a;
        while parent[ra as usize] != ra {
            ra = parent[ra as usize];
        }

        let mut rb = b;
        while parent[rb as usize] != rb {
            rb = parent[rb as usize];
        }

        if ra == rb {
            let mut res: Vec<i64> = Vec::new();
            res.push(a);
            res.push(b);
            return res;
        }

        let ra_us = ra as usize;
        let rb_us = rb as usize;

        let size_ra = size[ra_us];
        let size_rb = size[rb_us];

        if size_ra < size_rb {
            parent[ra_us] = rb;
            size[rb_us] = size_rb + size_ra;
        } else {
            parent[rb_us] = ra;
            size[ra_us] = size_ra + size_rb;
        }

        idx += 1;
    }

    let mut res: Vec<i64> = Vec::new();
    if n > 0 {
        res.push(edges[n - 1][0]);
        res.push(edges[n - 1][1]);
    }
    res
}
