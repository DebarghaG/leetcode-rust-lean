pub fn island_perimeter(grid: &[Vec<i64>]) -> i64 {
    let rows = grid.len();
    if rows == 0 {
        return 0;
    }
    let cols = grid[0].len();

    let mut perimeter: i64 = 0;
    let mut i: usize = 0;
    while i < rows {
        let mut j: usize = 0;
        while j < cols {
            if grid[i][j] == 1 {
                perimeter += 4;

                if i > 0 && grid[i - 1][j] == 1 {
                    perimeter -= 2;
                }
                if j > 0 && grid[i][j - 1] == 1 {
                    perimeter -= 2;
                }
            }
            j += 1;
        }
        i += 1;
    }

    perimeter
}
