pub fn count_points(points: &[Vec<i64>], queries: &[Vec<i64>]) -> Vec<i64> {
    let mut answer: Vec<i64> = Vec::new();
    let point_count = points.len();
    let query_count = queries.len();

    let mut j: usize = 0;
    while j < query_count {
        let cx = queries[j][0];
        let cy = queries[j][1];
        let r = queries[j][2];
        let r_squared = r * r;

        let mut count: i64 = 0;
        let mut i: usize = 0;

        while i < point_count {
            let px = points[i][0];
            let py = points[i][1];
            let dx = px - cx;
            let dy = py - cy;

            if dx * dx + dy * dy <= r_squared {
                count += 1;
            }

            i += 1;
        }

        answer.push(count);
        j += 1;
    }

    answer
}
