pub fn largest_local(grid: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n = grid.len();
    let out_size = n - 2;

    let mut out: Vec<Vec<i64>> = Vec::new();

    let mut i: usize = 0;
    while i < out_size {
        let mut row: Vec<i64> = Vec::new();

        let mut j: usize = 0;
        while j < out_size {
            let mut best: i64 = grid[i][j];

            let mut r: usize = i;
            while r < i + 3 {
                let mut c: usize = j;
                while c < j + 3 {
                    if grid[r][c] > best {
                        best = grid[r][c];
                    }
                    c += 1;
                }
                r += 1;
            }

            row.push(best);
            j += 1;
        }

        out.push(row);
        i += 1;
    }

    out
}
