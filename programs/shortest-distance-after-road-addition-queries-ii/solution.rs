pub fn shortest_distance_after_queries(n: i64, queries: &[Vec<i64>]) -> Vec<i64> {
    let nn = n as usize;

    // nxt[i] is the next still-active city after i.
    // A value of -1 means city i has already been removed from the main path.
    let mut nxt: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < nn {
        nxt.push((i as i64) + 1);
        i += 1;
    }

    let base = n - 1;
    let mut removed: i64 = 0;
    let mut ans: Vec<i64> = Vec::new();

    let qn = queries.len();
    let mut qi: usize = 0;
    while qi < qn {
        let u = queries[qi][0] as usize;
        let v = queries[qi][1];

        if nxt[u] != -1 {
            let mut x = nxt[u];
            while x < v {
                let xi = x as usize;
                let nx = nxt[xi];
                nxt[xi] = -1;
                removed += 1;
                x = nx;
            }
            nxt[u] = x;
        }

        ans.push(base - removed);
        qi += 1;
    }

    ans
}
