fn find(parent: &mut Vec<i64>, x: i64) -> i64 {
    let mut r = x;
    while parent[r as usize] != r {
        r = parent[r as usize];
    }

    let mut cur = x;
    while parent[cur as usize] != r {
        let nxt = parent[cur as usize];
        parent[cur as usize] = r;
        cur = nxt;
    }

    r
}

pub fn distance_limited_paths_exist(
    n: i64,
    edgeList: &[Vec<i64>],
    queries: &[Vec<i64>],
) -> Vec<bool> {
    let m = edgeList.len();
    let q = queries.len();

    let mut answer: Vec<bool> = Vec::new();
    let mut i = 0usize;
    while i < q {
        answer.push(false);
        i += 1;
    }

    let edge_base = m as i64 + 1;
    let mut edge_keys: Vec<i64> = Vec::new();
    i = 0usize;
    while i < m {
        let d = edgeList[i][2];
        let key = d * edge_base + i as i64;
        edge_keys.push(key);
        i += 1;
    }
    edge_keys.sort();

    let query_base = q as i64 + 1;
    let mut query_keys: Vec<i64> = Vec::new();
    i = 0usize;
    while i < q {
        let limit = queries[i][2];
        let key = limit * query_base + i as i64;
        query_keys.push(key);
        i += 1;
    }
    query_keys.sort();

    let mut parent: Vec<i64> = Vec::new();
    let mut size: Vec<i64> = Vec::new();

    let mut v = 0i64;
    while v < n {
        parent.push(v);
        size.push(1);
        v += 1;
    }

    let mut edge_pos = 0usize;
    let mut qi = 0usize;

    while qi < q {
        let qkey = query_keys[qi];
        let original_q = (qkey % query_base) as usize;
        let limit = queries[original_q][2];

        while edge_pos < m {
            let ekey = edge_keys[edge_pos];
            let original_e = (ekey % edge_base) as usize;
            let d = edgeList[original_e][2];

            if d < limit {
                let a = edgeList[original_e][0];
                let b = edgeList[original_e][1];

                let ra = find(&mut parent, a);
                let rb = find(&mut parent, b);

                if ra != rb {
                    let sa = size[ra as usize];
                    let sb = size[rb as usize];

                    if sa < sb {
                        parent[ra as usize] = rb;
                        size[rb as usize] = sa + sb;
                    } else {
                        parent[rb as usize] = ra;
                        size[ra as usize] = sa + sb;
                    }
                }

                edge_pos += 1;
            } else {
                break;
            }
        }

        let p = queries[original_q][0];
        let qv = queries[original_q][1];

        let rp = find(&mut parent, p);
        let rqv = find(&mut parent, qv);

        answer[original_q] = rp == rqv;
        qi += 1;
    }

    answer
}
