pub fn number_of_right_triangles(grid: &[Vec<i64>]) -> i64 {
    let n = grid.len();
    if n == 0 {
        return 0;
    }

    let m = grid[0].len();
    if m == 0 {
        return 0;
    }

    let mut col_sums: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < m {
        col_sums.push(0);
        j += 1;
    }

    let mut row_sums: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let row = &grid[i];
        let mut rs: i64 = 0;

        j = 0;
        while j < m {
            rs += row[j];
            col_sums[j] += row[j];
            j += 1;
        }

        row_sums.push(rs);
        i += 1;
    }

    let mut ans: i64 = 0;

    i = 0;
    while i < n {
        let row = &grid[i];

        j = 0;
        while j < m {
            if row[j] == 1 {
                ans += (row_sums[i] - 1) * (col_sums[j] - 1);
            }
            j += 1;
        }

        i += 1;
    }

    ans
}
