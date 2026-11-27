pub fn k_closest(points: &[Vec<i64>], k: i64) -> Vec<Vec<i64>> {
    let n = points.len();

    let mut used: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < n {
        used.push(false);
        i += 1;
    }

    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut count: i64 = 0;

    while count < k {
        let mut best: usize = n;
        let mut best_dist: i64 = 0;

        let mut j = 0;
        while j < n {
            if !used[j] {
                let x = points[j][0];
                let y = points[j][1];
                let dist = x * x + y * y;

                if best == n || dist < best_dist {
                    best = j;
                    best_dist = dist;
                }
            }
            j += 1;
        }

        used[best] = true;

        let mut row: Vec<i64> = Vec::new();
        row.push(points[best][0]);
        row.push(points[best][1]);
        out.push(row);

        count += 1;
    }

    out
}
