pub fn check_x_matrix(grid: &[Vec<i64>]) -> bool {
    let n = grid.len();
    let mut ok: bool = true;

    let mut i: usize = 0;
    while i < n {
        let mut j: usize = 0;
        while j < n {
            let mut is_diagonal: bool = false;
            if i == j {
                is_diagonal = true;
            }
            if j == n - 1 - i {
                is_diagonal = true;
            }

            if is_diagonal {
                if grid[i][j] == 0 {
                    ok = false;
                }
            } else {
                if grid[i][j] != 0 {
                    ok = false;
                }
            }

            j += 1;
        }
        i += 1;
    }

    ok
}
