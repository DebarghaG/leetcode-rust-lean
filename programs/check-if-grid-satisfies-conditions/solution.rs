pub fn satisfies_conditions(grid: &[Vec<i64>]) -> bool {
    let m = grid.len();
    if m == 0 {
        return true;
    }

    let n = grid[0].len();
    let mut ok: bool = true;
    let mut i: usize = 0;

    while i < m && ok {
        let mut j: usize = 0;

        while j < n && ok {
            if j + 1 < n {
                if grid[i][j] == grid[i][j + 1] {
                    ok = false;
                }
            }

            if ok && i + 1 < m {
                if grid[i][j] != grid[i + 1][j] {
                    ok = false;
                }
            }

            j = j + 1;
        }

        i = i + 1;
    }

    ok
}
