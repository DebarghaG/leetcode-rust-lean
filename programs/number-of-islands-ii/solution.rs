fn uf_find(parent: &mut Vec<i64>, x: usize) -> usize {
    let mut root = x;
    while parent[root] != root as i64 {
        root = parent[root] as usize;
    }

    let mut cur = x;
    while parent[cur] != cur as i64 {
        let next = parent[cur] as usize;
        parent[cur] = root as i64;
        cur = next;
    }

    root
}

fn uf_union(parent: &mut Vec<i64>, size: &mut Vec<i64>, a: usize, b: usize) -> bool {
    let ra = uf_find(parent, a);
    let rb = uf_find(parent, b);

    if ra == rb {
        return false;
    }

    if size[ra] < size[rb] {
        parent[ra] = rb as i64;
        size[rb] = size[rb] + size[ra];
    } else {
        parent[rb] = ra as i64;
        size[ra] = size[ra] + size[rb];
    }

    true
}

pub fn num_islands2(m: i64, n: i64, positions: &[Vec<i64>]) -> Vec<i64> {
    let m_usize = m as usize;
    let n_usize = n as usize;
    let total = m_usize * n_usize;

    let mut parent: Vec<i64> = Vec::new();
    let mut size: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < total {
        parent.push(-1);
        size.push(0);
        i += 1;
    }

    let mut answer: Vec<i64> = Vec::new();
    let mut islands: i64 = 0;

    let mut p = 0;
    while p < positions.len() {
        let r_i64 = positions[p][0];
        let c_i64 = positions[p][1];

        let r = r_i64 as usize;
        let c = c_i64 as usize;
        let idx = r * n_usize + c;

        if parent[idx] != -1 {
            answer.push(islands);
        } else {
            parent[idx] = idx as i64;
            size[idx] = 1;
            islands = islands + 1;

            if r > 0 {
                let nidx = (r - 1) * n_usize + c;
                if parent[nidx] != -1 {
                    if uf_union(&mut parent, &mut size, idx, nidx) {
                        islands = islands - 1;
                    }
                }
            }

            if r + 1 < m_usize {
                let nidx = (r + 1) * n_usize + c;
                if parent[nidx] != -1 {
                    if uf_union(&mut parent, &mut size, idx, nidx) {
                        islands = islands - 1;
                    }
                }
            }

            if c > 0 {
                let nidx = r * n_usize + (c - 1);
                if parent[nidx] != -1 {
                    if uf_union(&mut parent, &mut size, idx, nidx) {
                        islands = islands - 1;
                    }
                }
            }

            if c + 1 < n_usize {
                let nidx = r * n_usize + (c + 1);
                if parent[nidx] != -1 {
                    if uf_union(&mut parent, &mut size, idx, nidx) {
                        islands = islands - 1;
                    }
                }
            }

            answer.push(islands);
        }

        p += 1;
    }

    answer
}
