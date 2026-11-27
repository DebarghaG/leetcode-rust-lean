pub fn valid_path(n: i64, edges: &[Vec<i64>], source: i64, destination: i64) -> bool {
    let mut parent: Vec<i64> = Vec::new();
    let mut size: Vec<i64> = Vec::new();

    let mut i: i64 = 0;
    while i < n {
        parent.push(i);
        size.push(1);
        i += 1;
    }

    let m: usize = edges.len();
    let mut e: usize = 0;

    while e < m {
        let mut ru = edges[e][0];
        while parent[ru as usize] != ru {
            ru = parent[ru as usize];
        }

        let mut rv = edges[e][1];
        while parent[rv as usize] != rv {
            rv = parent[rv as usize];
        }

        if ru != rv {
            let su = size[ru as usize];
            let sv = size[rv as usize];

            if su < sv {
                parent[ru as usize] = rv;
                size[rv as usize] = su + sv;
            } else {
                parent[rv as usize] = ru;
                size[ru as usize] = su + sv;
            }
        }

        e += 1;
    }

    let mut rs = source;
    while parent[rs as usize] != rs {
        rs = parent[rs as usize];
    }

    let mut rd = destination;
    while parent[rd as usize] != rd {
        rd = parent[rd as usize];
    }

    rs == rd
}
