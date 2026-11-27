pub fn remove_ones(grid: &[Vec<i64>]) -> bool {
    let m = grid.len();
    if m == 0 {
        return true;
    }

    let n = grid[0].len();
    let mut i = 1;

    while i < m {
        let mut all_same = true;
        let mut all_flipped = true;
        let mut j = 0;

        while j < n {
            if grid[i][j] == grid[0][j] {
                all_flipped = false;
            } else {
                all_same = false;
            }
            j += 1;
        }

        if !all_same && !all_flipped {
            return false;
        }

        i += 1;
    }

    true
}
