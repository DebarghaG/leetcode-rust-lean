pub fn nearest_valid_point(x: i64, y: i64, points: &[Vec<i64>]) -> i64 {
    let n = points.len();
    let mut i: usize = 0;
    let mut index: i64 = 0;
    let mut best_index: i64 = -1;
    let mut best_dist: i64 = 0;
    let mut found: bool = false;

    while i < n {
        let px = points[i][0];
        let py = points[i][1];

        if px == x || py == y {
            let mut dx = px - x;
            if dx < 0 {
                dx = -dx;
            }

            let mut dy = py - y;
            if dy < 0 {
                dy = -dy;
            }

            let dist = dx + dy;

            if !found || dist < best_dist {
                found = true;
                best_dist = dist;
                best_index = index;
            }
        }

        i += 1;
        index += 1;
    }

    best_index
}
