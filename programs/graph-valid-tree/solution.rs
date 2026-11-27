pub fn valid_tree(n: i64, edges: &[Vec<i64>]) -> bool {
    if n <= 0 {
        return edges.len() == 0;
    }

    let nn: usize = n as usize;
    if edges.len() != nn - 1 {
        return false;
    }

    let mut parent: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < nn {
        parent.push(i as i64);
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let u: i64 = edges[e][0];
        let v: i64 = edges[e][1];

        let ru: i64 = find(&mut parent, u);
        let rv: i64 = find(&mut parent, v);

        if ru == rv {
            return false;
        }

        parent[ru as usize] = rv;
        e += 1;
    }

    true
}

fn find(parent: &mut Vec<i64>, x: i64) -> i64 {
    let mut root: i64 = x;
    while parent[root as usize] != root {
        root = parent[root as usize];
    }

    let mut cur: i64 = x;
    while parent[cur as usize] != cur {
        let next: i64 = parent[cur as usize];
        parent[cur as usize] = root;
        cur = next;
    }

    root
}
