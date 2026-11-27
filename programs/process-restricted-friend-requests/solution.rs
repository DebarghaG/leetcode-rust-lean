fn find(parent: &mut Vec<i64>, x: i64) -> i64 {
    let mut root = x;
    while parent[root as usize] != root {
        root = parent[root as usize];
    }

    let mut cur = x;
    while parent[cur as usize] != root {
        let next = parent[cur as usize];
        parent[cur as usize] = root;
        cur = next;
    }

    root
}

pub fn friend_requests(n: i64, restrictions: &[Vec<i64>], requests: &[Vec<i64>]) -> Vec<bool> {
    let mut parent: Vec<i64> = Vec::new();
    let mut i = 0i64;
    while i < n {
        parent.push(i);
        i += 1;
    }

    let mut result: Vec<bool> = Vec::new();
    let mut idx = 0usize;

    while idx < requests.len() {
        let u = requests[idx][0];
        let v = requests[idx][1];

        let ru = find(&mut parent, u);
        let rv = find(&mut parent, v);

        if ru == rv {
            result.push(true);
        } else {
            let mut ok = true;
            let mut j = 0usize;

            while j < restrictions.len() {
                let a = restrictions[j][0];
                let b = restrictions[j][1];

                let ra = find(&mut parent, a);
                let rb = find(&mut parent, b);

                if (ra == ru && rb == rv) || (ra == rv && rb == ru) {
                    ok = false;
                    j = restrictions.len();
                } else {
                    j += 1;
                }
            }

            if ok {
                parent[rv as usize] = ru;
                result.push(true);
            } else {
                result.push(false);
            }
        }

        idx += 1;
    }

    result
}
