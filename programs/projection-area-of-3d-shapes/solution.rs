pub fn projection_area(grid: &[Vec<i64>]) -> i64 {
    let n = grid.len();
    let mut total: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let row = &grid[i];
        let mut row_max: i64 = 0;

        let mut j: usize = 0;
        while j < row.len() {
            let v = row[j];
            if v > 0 {
                total += 1;
            }
            if v > row_max {
                row_max = v;
            }
            j += 1;
        }

        total += row_max;
        i += 1;
    }

    let mut col: usize = 0;
    while col < n {
        let mut col_max: i64 = 0;

        let mut row_idx: usize = 0;
        while row_idx < n {
            let v = grid[row_idx][col];
            if v > col_max {
                col_max = v;
            }
            row_idx += 1;
        }

        total += col_max;
        col += 1;
    }

    total
}
