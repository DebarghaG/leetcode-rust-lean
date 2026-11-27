pub fn find_champion(grid: &[Vec<i64>]) -> i64 {
    let n = grid.len();
    let mut i: usize = 0;

    while i < n {
        let row = &grid[i];
        let mut is_champion: bool = true;
        let mut j: usize = 0;

        while j < n {
            if i != j {
                if row[j] != 1 {
                    is_champion = false;
                }
            }
            j += 1;
        }

        if is_champion {
            return i as i64;
        }

        i += 1;
    }

    -1
}
