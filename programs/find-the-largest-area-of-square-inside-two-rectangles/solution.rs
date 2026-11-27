fn min_i64(a: i64, b: i64) -> i64 {
    if a < b {
        a
    } else {
        b
    }
}

fn max_i64(a: i64, b: i64) -> i64 {
    if a > b {
        a
    } else {
        b
    }
}

pub fn largest_square_area(bottomLeft: &[Vec<i64>], topRight: &[Vec<i64>]) -> i64 {
    let n: usize = bottomLeft.len();
    let mut best: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let mut j: usize = i + 1;
        while j < n {
            let left = max_i64(bottomLeft[i][0], bottomLeft[j][0]);
            let right = min_i64(topRight[i][0], topRight[j][0]);
            let bottom = max_i64(bottomLeft[i][1], bottomLeft[j][1]);
            let top = min_i64(topRight[i][1], topRight[j][1]);

            let width = right - left;
            let height = top - bottom;

            if width > 0 && height > 0 {
                let side = min_i64(width, height);
                let area = side * side;
                if area > best {
                    best = area;
                }
            }

            j += 1;
        }
        i += 1;
    }

    best
}
