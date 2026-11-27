pub fn min_rectangles_to_cover_points(points: &[Vec<i64>], w: i64) -> i64 {
    let n = points.len();
    let mut xs: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        xs.push(points[i][0]);
        i += 1;
    }

    xs.sort();

    let mut ans: i64 = 0;
    let mut idx: usize = 0;

    while idx < n {
        let start = xs[idx];
        let end = start + w;
        ans += 1;

        while idx < n && xs[idx] <= end {
            idx += 1;
        }
    }

    ans
}
