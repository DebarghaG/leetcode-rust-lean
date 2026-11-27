pub fn maximum_importance(n: i64, roads: &[Vec<i64>]) -> i64 {
    let n_usize = n as usize;

    let mut degrees: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        degrees.push(0);
        i += 1;
    }

    let m: usize = roads.len();

    let mut r: usize = 0;
    while r < m {
        let a = roads[r][0] as usize;
        let b = roads[r][1] as usize;

        degrees[a] += 1;
        degrees[b] += 1;

        r += 1;
    }

    let mut freq: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k <= m {
        freq.push(0);
        k += 1;
    }

    let mut c: usize = 0;
    while c < n_usize {
        let d = degrees[c] as usize;
        freq[d] += 1;
        c += 1;
    }

    let mut total: i64 = 0;
    let mut value: i64 = 1;
    let mut d: usize = 0;

    while d <= m {
        let mut count = freq[d];
        while count > 0 {
            total += (d as i64) * value;
            value += 1;
            count -= 1;
        }
        d += 1;
    }

    total
}
