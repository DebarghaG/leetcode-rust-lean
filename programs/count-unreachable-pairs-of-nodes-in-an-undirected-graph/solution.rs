pub fn count_pairs(n: i64, edges: &[Vec<i64>]) -> i64 {
    let nu: usize = n as usize;

    // parent[i] < 0 means i is a root and -parent[i] is the component size.
    // parent[i] >= 0 means the parent of i.
    let mut parent: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < nu {
        parent.push(-1);
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let a: usize = edges[e][0] as usize;
        let b: usize = edges[e][1] as usize;

        let mut ra: usize = a;
        while parent[ra] >= 0 {
            ra = parent[ra] as usize;
        }

        let mut rb: usize = b;
        while parent[rb] >= 0 {
            rb = parent[rb] as usize;
        }

        if ra != rb {
            if parent[ra] > parent[rb] {
                // ra has the smaller component size, so attach ra under rb.
                parent[rb] = parent[rb] + parent[ra];
                parent[ra] = rb as i64;
            } else {
                // rb has the smaller or equal component size, so attach rb under ra.
                parent[ra] = parent[ra] + parent[rb];
                parent[rb] = ra as i64;
            }
        }

        e += 1;
    }

    let mut reachable_pairs: i64 = 0;
    let mut j: usize = 0;
    while j < nu {
        if parent[j] < 0 {
            let size: i64 = -parent[j];
            reachable_pairs += size * (size - 1) / 2;
        }
        j += 1;
    }

    let total_pairs: i64 = n * (n - 1) / 2;
    total_pairs - reachable_pairs
}
