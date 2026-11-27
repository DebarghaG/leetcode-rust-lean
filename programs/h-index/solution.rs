pub fn h_index(citations: &[i64]) -> i64 {
    let n = citations.len();
    let mut counts: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i <= n {
        counts.push(0);
        i += 1;
    }

    let n_i64 = n as i64;
    let mut idx: usize = 0;
    while idx < n {
        let c = citations[idx];
        if c >= n_i64 {
            counts[n] += 1;
        } else {
            let pos = c as usize;
            counts[pos] += 1;
        }
        idx += 1;
    }

    let mut total: i64 = 0;
    let mut h: usize = n;
    while h > 0 {
        total += counts[h];
        if total >= h as i64 {
            return h as i64;
        }
        h -= 1;
    }

    0
}
