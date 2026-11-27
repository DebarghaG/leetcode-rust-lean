pub fn minimum_area(grid: &[Vec<i64>]) -> i64 {
    let rows = grid.len();
    if rows == 0 {
        return 0;
    }

    // Smallest row index that contains a 1.
    let mut min_r: i64 = rows as i64;
    for i in 0..rows {
        let len = grid[i].len();
        for j in 0..len {
            if grid[i][j] == 1 {
                if (i as i64) < min_r {
                    min_r = i as i64;
                }
            }
        }
    }

    // Largest row index that contains a 1.
    let mut max_r: i64 = -1;
    for i in 0..rows {
        let len = grid[i].len();
        for j in 0..len {
            if grid[i][j] == 1 {
                if (i as i64) > max_r {
                    max_r = i as i64;
                }
            }
        }
    }

    // Smallest column index that contains a 1.
    let mut min_c: i64 = 1000000000;
    for i in 0..rows {
        let len = grid[i].len();
        for j in 0..len {
            if grid[i][j] == 1 {
                if (j as i64) < min_c {
                    min_c = j as i64;
                }
            }
        }
    }

    // Largest column index that contains a 1.
    let mut max_c: i64 = -1;
    for i in 0..rows {
        let len = grid[i].len();
        for j in 0..len {
            if grid[i][j] == 1 {
                if (j as i64) > max_c {
                    max_c = j as i64;
                }
            }
        }
    }

    (max_r - min_r + 1) * (max_c - min_c + 1)
}
