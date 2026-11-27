fn find(parent: &mut Vec<i64>, x: i64) -> i64 {
    let mut r = x;
    while parent[r as usize] != r {
        r = parent[r as usize];
    }

    let root = r;
    let mut y = x;
    while parent[y as usize] != root {
        let next = parent[y as usize];
        parent[y as usize] = root;
        y = next;
    }

    root
}

pub fn count_components(n: i64, edges: &[Vec<i64>]) -> i64 {
    let nn = n as usize;

    let mut parent: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < nn {
        parent.push(i as i64);
        i += 1;
    }

    let mut components = n;
    let mut e: usize = 0;
    while e < edges.len() {
        let a = edges[e][0];
        let b = edges[e][1];

        let ra = find(&mut parent, a);
        let rb = find(&mut parent, b);

        if ra != rb {
            parent[rb as usize] = ra;
            components -= 1;
        }

        e += 1;
    }

    components
}
