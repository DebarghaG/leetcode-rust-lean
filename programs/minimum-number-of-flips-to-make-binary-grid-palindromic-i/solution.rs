pub fn min_flips(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }
    let n = grid[0].len();

    let mut row_cost: i64 = 0;
    let mut i: usize = 0;
    while i < m {
        let row = &grid[i];
        let mut j: usize = 0;
        while j < n / 2 {
            if row[j] != row[n - 1 - j] {
                row_cost += 1;
            }
            j += 1;
        }
        i += 1;
    }

    let mut col_cost: i64 = 0;
    let mut j: usize = 0;
    while j < n {
        let mut i: usize = 0;
        while i < m / 2 {
            if grid[i][j] != grid[m - 1 - i][j] {
                col_cost += 1;
            }
            i += 1;
        }
        j += 1;
    }

    if row_cost < col_cost {
        row_cost
    } else {
        col_cost
    }
}
