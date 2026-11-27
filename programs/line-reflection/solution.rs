pub fn is_reflected(points: &[Vec<i64>]) -> bool {
    let n = points.len();
    if n == 0 {
        return true;
    }

    let mut min_x = points[0][0];
    let mut max_x = points[0][0];

    let mut i = 0usize;
    while i < n {
        let x = points[i][0];
        if x < min_x {
            min_x = x;
        }
        if x > max_x {
            max_x = x;
        }
        i += 1;
    }

    let twice_center = min_x + max_x;

    let mut sorted: Vec<Vec<i64>> = Vec::new();
    i = 0;
    while i < n {
        let mut p: Vec<i64> = Vec::new();
        p.push(points[i][0]);
        p.push(points[i][1]);
        sorted.push(p);
        i += 1;
    }
    sorted.sort();

    i = 0;
    while i < n {
        let reflected_x = twice_center - points[i][0];
        let y = points[i][1];
        if !contains_point(&sorted, reflected_x, y) {
            return false;
        }
        i += 1;
    }

    true
}

fn contains_point(points: &[Vec<i64>], x: i64, y: i64) -> bool {
    let mut lo = 0usize;
    let mut hi = points.len();

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        let px = points[mid][0];
        let py = points[mid][1];

        if px < x {
            lo = mid + 1;
        } else if px > x {
            hi = mid;
        } else {
            if py < y {
                lo = mid + 1;
            } else if py > y {
                hi = mid;
            } else {
                return true;
            }
        }
    }

    false
}
