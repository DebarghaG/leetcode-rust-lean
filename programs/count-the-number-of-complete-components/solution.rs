pub fn count_complete_components(n: i64, edges: &[Vec<i64>]) -> i64 {
    let n_usize = n as usize;

    let mut parent: Vec<usize> = Vec::new();
    let mut size: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n_usize {
        parent.push(i);
        size.push(1);
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let a = edges[e][0] as usize;
        let b = edges[e][1] as usize;

        let mut ra = a;
        while parent[ra] != ra {
            ra = parent[ra];
        }

        let mut rb = b;
        while parent[rb] != rb {
            rb = parent[rb];
        }

        if ra != rb {
            if size[ra] < size[rb] {
                parent[ra] = rb;
                size[rb] += size[ra];
            } else {
                parent[rb] = ra;
                size[ra] += size[rb];
            }
        }

        e += 1;
    }

    let mut edge_count: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < n_usize {
        edge_count.push(0);
        j += 1;
    }

    let mut e2: usize = 0;
    while e2 < edges.len() {
        let a = edges[e2][0] as usize;

        let mut ra = a;
        while parent[ra] != ra {
            ra = parent[ra];
        }

        edge_count[ra] += 1;
        e2 += 1;
    }

    let mut ans: i64 = 0;
    let mut v: usize = 0;
    while v < n_usize {
        if parent[v] == v {
            let s = size[v];
            if edge_count[v] == s * (s - 1) / 2 {
                ans += 1;
            }
        }
        v += 1;
    }

    ans
}
