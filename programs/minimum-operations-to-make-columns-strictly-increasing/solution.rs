pub fn minimum_operations(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }

    let n = grid[0].len();
    let mut operations: i64 = 0;

    let mut j = 0;
    while j < n {
        let mut prev = grid[0][j];
        let mut i = 1;

        while i < m {
            let mut current = grid[i][j];

            if current <= prev {
                let needed = prev + 1 - current;
                operations += needed;
                current = prev + 1;
            }

            prev = current;
            i += 1;
        }

        j += 1;
    }

    operations
}
