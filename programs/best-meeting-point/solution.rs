pub fn min_total_distance(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }

    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let mut row_count: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < m {
        row_count.push(0);
        i += 1;
    }

    let mut col_count: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < n {
        col_count.push(0);
        j += 1;
    }

    i = 0;
    while i < m {
        let row = &grid[i];
        j = 0;
        while j < n {
            if row[j] == 1 {
                row_count[i] = row_count[i] + 1;
                col_count[j] = col_count[j] + 1;
            }
            j += 1;
        }
        i += 1;
    }

    let mut best_row: i64 = 0;
    let mut p: usize = 0;
    while p < m {
        let mut dist: i64 = 0;
        let mut r: usize = 0;
        while r < m {
            let diff: i64;
            if r > p {
                diff = (r - p) as i64;
            } else {
                diff = (p - r) as i64;
            }
            dist = dist + diff * row_count[r];
            r += 1;
        }
        if p == 0 || dist < best_row {
            best_row = dist;
        }
        p += 1;
    }

    let mut best_col: i64 = 0;
    p = 0;
    while p < n {
        let mut dist: i64 = 0;
        let mut c: usize = 0;
        while c < n {
            let diff: i64;
            if c > p {
                diff = (c - p) as i64;
            } else {
                diff = (p - c) as i64;
            }
            dist = dist + diff * col_count[c];
            c += 1;
        }
        if p == 0 || dist < best_col {
            best_col = dist;
        }
        p += 1;
    }

    best_row + best_col
}
