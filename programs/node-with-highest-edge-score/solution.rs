pub fn edge_score(edges: &[i64]) -> i64 {
    let n = edges.len();

    let mut scores: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        scores.push(0);
        i += 1;
    }

    i = 0;
    while i < n {
        let to = edges[i] as usize;
        scores[to] = scores[to] + (i as i64);
        i += 1;
    }

    let mut best: usize = 0;
    i = 1;
    while i < n {
        if scores[i] > scores[best] {
            best = i;
        }
        i += 1;
    }

    best as i64
}
