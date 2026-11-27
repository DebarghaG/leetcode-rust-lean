pub fn ones_minus_zeros(grid: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let m = grid.len();
    if m == 0 {
        return Vec::new();
    }
    let n = grid[0].len();

    let mut ones_row: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < m {
        let row = &grid[i];
        let mut cnt: i64 = 0;
        let mut j = 0;
        while j < n {
            if row[j] == 1 {
                cnt += 1;
            }
            j += 1;
        }
        ones_row.push(cnt);
        i += 1;
    }

    let mut ones_col: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < n {
        let mut cnt: i64 = 0;
        let mut i2 = 0;
        while i2 < m {
            if grid[i2][j] == 1 {
                cnt += 1;
            }
            i2 += 1;
        }
        ones_col.push(cnt);
        j += 1;
    }

    let m_i64 = m as i64;
    let n_i64 = n as i64;

    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < m {
        let mut row_out: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            let row_part = 2 * ones_row[i] - n_i64;
            let col_part = 2 * ones_col[j] - m_i64;
            row_out.push(row_part + col_part);
            j += 1;
        }
        out.push(row_out);
        i += 1;
    }

    out
}
