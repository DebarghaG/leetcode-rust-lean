pub fn max_score_sightseeing_pair(values: &[i64]) -> i64 {
    let n = values.len();
    if n < 2 {
        return 0;
    }

    let mut best = values[0];
    let mut ans = values[0] + values[1] - 1;

    let mut j: usize = 1;
    let mut pos: i64 = 1;

    while j < n {
        let candidate = best + values[j] - pos;
        if candidate > ans {
            ans = candidate;
        }

        let current = values[j] + pos;
        if current > best {
            best = current;
        }

        j += 1;
        pos += 1;
    }

    ans
}
