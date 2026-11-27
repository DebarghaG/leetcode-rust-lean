pub fn min_time_to_visit_all_points(points: &[Vec<i64>]) -> i64 {
    let mut total: i64 = 0;
    let mut i: usize = 1;

    while i < points.len() {
        let dx = points[i][0] - points[i - 1][0];
        let dy = points[i][1] - points[i - 1][1];

        let adx = if dx < 0 { -dx } else { dx };
        let ady = if dy < 0 { -dy } else { dy };

        if adx > ady {
            total += adx;
        } else {
            total += ady;
        }

        i += 1;
    }

    total
}
