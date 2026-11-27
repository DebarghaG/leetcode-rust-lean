pub fn process_queries(queries: &[i64], m: i64) -> Vec<i64> {
    let mut perm: Vec<i64> = Vec::new();
    let mut i: i64 = 0;
    while i < m {
        perm.push(i + 1);
        i += 1;
    }

    let mut result: Vec<i64> = Vec::new();
    let mut qi: usize = 0;

    while qi < queries.len() {
        let q = queries[qi];

        let mut pos: usize = 0;
        while perm[pos] != q {
            pos += 1;
        }

        result.push(pos as i64);

        let value = perm[pos];
        let mut j: usize = pos;
        while j > 0 {
            let prev = perm[j - 1];
            perm[j] = prev;
            j -= 1;
        }
        perm[0] = value;

        qi += 1;
    }

    result
}
