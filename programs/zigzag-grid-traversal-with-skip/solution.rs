pub fn zigzag_traversal(grid: &[Vec<i64>]) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();
    let mut take: bool = true;

    let m = grid.len();
    let mut i: usize = 0;

    while i < m {
        let n = grid[i].len();
        let mut j: usize = 0;

        while j < n {
            let mut col = j;
            if i % 2 == 1 {
                col = n - 1 - j;
            }

            if take {
                result.push(grid[i][col]);
            }

            take = !take;
            j += 1;
        }

        i += 1;
    }

    result
}
