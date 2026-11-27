fn find(parent: &mut Vec<i64>, x: i64) -> i64 {
    let mut root = x;
    while parent[root as usize] != root {
        root = parent[root as usize];
    }

    let mut cur = x;
    while parent[cur as usize] != cur {
        let next = parent[cur as usize];
        parent[cur as usize] = root;
        cur = next;
    }

    root
}

pub fn make_connected(n: i64, connections: &[Vec<i64>]) -> i64 {
    let nn = n as usize;

    let m = connections.len() as i64;
    if m < n - 1 {
        return -1;
    }

    let mut parent: Vec<i64> = Vec::new();
    let mut size: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < nn {
        parent.push(i as i64);
        size.push(1);
        i += 1;
    }

    let mut components = n;
    let mut k: usize = 0;

    while k < connections.len() {
        let a = connections[k][0];
        let b = connections[k][1];

        let ra = find(&mut parent, a);
        let rb = find(&mut parent, b);

        if ra != rb {
            let sa = size[ra as usize];
            let sb = size[rb as usize];

            if sa < sb {
                parent[ra as usize] = rb;
                size[rb as usize] = size[rb as usize] + size[ra as usize];
            } else {
                parent[rb as usize] = ra;
                size[ra as usize] = size[ra as usize] + size[rb as usize];
            }

            components -= 1;
        }

        k += 1;
    }

    components - 1
}
