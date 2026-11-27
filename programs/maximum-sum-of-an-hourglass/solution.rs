pub fn max_sum(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m < 3 {
        return 0;
    }

    let n = grid[0].len();
    if n < 3 {
        return 0;
    }

    let mut best: i64 = 0;
    let mut i: usize = 0;

    while i + 2 < m {
        let mut j: usize = 0;

        while j + 2 < n {
            let top_left = grid[i][j];
            let top_mid = grid[i][j + 1];
            let top_right = grid[i][j + 2];

            let mid = grid[i + 1][j + 1];

            let bottom_left = grid[i + 2][j];
            let bottom_mid = grid[i + 2][j + 1];
            let bottom_right = grid[i + 2][j + 2];

            let sum = top_left
                + top_mid
                + top_right
                + mid
                + bottom_left
                + bottom_mid
                + bottom_right;

            if sum > best {
                best = sum;
            }

            j += 1;
        }

        i += 1;
    }

    best
}
