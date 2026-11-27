pub fn equations_possible(equations: &[Vec<u8>]) -> bool {
    let mut parent: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < 26 {
        parent.push(i);
        i += 1;
    }

    let n: usize = equations.len();

    i = 0;
    while i < n {
        if equations[i][1] == b'=' {
            let x: usize = (equations[i][0] as usize) - 97;
            let y: usize = (equations[i][3] as usize) - 97;

            let mut rx: usize = x;
            while parent[rx] != rx {
                rx = parent[rx];
            }

            let mut ry: usize = y;
            while parent[ry] != ry {
                ry = parent[ry];
            }

            if rx != ry {
                parent[ry] = rx;
            }
        }
        i += 1;
    }

    i = 0;
    while i < n {
        if equations[i][1] == b'!' {
            let x: usize = (equations[i][0] as usize) - 97;
            let y: usize = (equations[i][3] as usize) - 97;

            let mut rx: usize = x;
            while parent[rx] != rx {
                rx = parent[rx];
            }

            let mut ry: usize = y;
            while parent[ry] != ry {
                ry = parent[ry];
            }

            if rx == ry {
                return false;
            }
        }
        i += 1;
    }

    true
}
