fn collect_distances(bound: i64, fences: &[i64]) -> Vec<i64> {
    let mut positions: Vec<i64> = Vec::new();
    positions.push(1);

    let mut k = 0;
    while k < fences.len() {
        positions.push(fences[k]);
        k += 1;
    }

    positions.push(bound);

    let len = positions.len();
    let mut distances: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < len {
        let mut j = i + 1;
        while j < len {
            let a = positions[i];
            let b = positions[j];
            let d = if a > b { a - b } else { b - a };
            distances.push(d);
            j += 1;
        }
        i += 1;
    }

    distances
}

pub fn maximize_square_area(m: i64, n: i64, hFences: &[i64], vFences: &[i64]) -> i64 {
    let mut h_distances = collect_distances(m, hFences);
    let mut v_distances = collect_distances(n, vFences);

    h_distances.sort();
    v_distances.sort();

    let mut i = h_distances.len();
    let mut j = v_distances.len();
    let mut best: i64 = -1;

    while i > 0 && j > 0 {
        let a = h_distances[i - 1];
        let b = v_distances[j - 1];

        if a == b {
            best = a;
            break;
        } else if a > b {
            i -= 1;
        } else {
            j -= 1;
        }
    }

    if best < 0 {
        return -1;
    }

    let modulo: i64 = 1000000007;
    let x = best % modulo;
    (x * x) % modulo
}
