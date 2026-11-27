pub fn max_width_of_vertical_area(points: &[Vec<i64>]) -> i64 {
    let n = points.len();
    let mut xs: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        xs.push(points[i][0]);
        i += 1;
    }

    xs.sort();

    let mut best = 0;
    let mut j = 1;
    while j < n {
        let width = xs[j] - xs[j - 1];
        if width > best {
            best = width;
        }
        j += 1;
    }

    best
}
