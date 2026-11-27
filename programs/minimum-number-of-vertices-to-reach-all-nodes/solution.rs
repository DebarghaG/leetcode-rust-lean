pub fn find_smallest_set_of_vertices(n: i64, edges: &[Vec<i64>]) -> Vec<i64> {
    let nn = n as usize;

    let mut has_parent: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < nn {
        has_parent.push(false);
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let to = edges[e][1] as usize;
        has_parent[to] = true;
        e += 1;
    }

    let mut result: Vec<i64> = Vec::new();
    let mut v: usize = 0;
    while v < nn {
        if !has_parent[v] {
            result.push(v as i64);
        }
        v += 1;
    }

    result
}
