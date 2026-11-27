pub fn count_corner_rectangles(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }

    let n = grid[0].len();
    let mut total: i64 = 0;
    let mut r1: usize = 0;

    while r1 < m {
        let mut r2: usize = r1 + 1;
        while r2 < m {
            let mut common: i64 = 0;
            let mut c: usize = 0;

            while c < n {
                if grid[r1][c] == 1 && grid[r2][c] == 1 {
                    common = common + 1;
                }
                c = c + 1;
            }

            total = total + common * (common - 1) / 2;
            r2 = r2 + 1;
        }
        r1 = r1 + 1;
    }

    total
}
