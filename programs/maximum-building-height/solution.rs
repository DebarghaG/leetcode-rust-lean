pub fn max_building(n: i64, restrictions: &[Vec<i64>]) -> i64 {
    let mut points: Vec<Vec<i64>> = Vec::new();

    let mut start: Vec<i64> = Vec::new();
    start.push(1);
    start.push(0);
    points.push(start);

    let mut has_n = false;
    let m = restrictions.len();
    let mut i = 0;
    while i < m {
        let id = restrictions[i][0];
        let height = restrictions[i][1];

        if id == n {
            has_n = true;
        }

        let mut row: Vec<i64> = Vec::new();
        row.push(id);
        row.push(height);
        points.push(row);

        i += 1;
    }

    if !has_n {
        let mut row: Vec<i64> = Vec::new();
        row.push(n);
        row.push(n - 1);
        points.push(row);
    }

    points.sort();

    let k = points.len();

    let mut i = 1;
    while i < k {
        let prev_id = points[i - 1][0];
        let prev_h = points[i - 1][1];
        let dist = points[i][0] - prev_id;
        let cap = prev_h + dist;

        if points[i][1] > cap {
            points[i][1] = cap;
        }

        i += 1;
    }

    let mut i = k - 1;
    while i > 0 {
        let next_id = points[i][0];
        let next_h = points[i][1];
        let dist = next_id - points[i - 1][0];
        let cap = next_h + dist;

        if points[i - 1][1] > cap {
            points[i - 1][1] = cap;
        }

        i -= 1;
    }

    let mut ans: i64 = 0;

    let mut i = 1;
    while i < k {
        let left_id = points[i - 1][0];
        let left_h = points[i - 1][1];
        let right_h = points[i][1];
        let dist = points[i][0] - left_id;

        let candidate = (left_h + right_h + dist) / 2;
        if candidate > ans {
            ans = candidate;
        }

        i += 1;
    }

    ans
}
