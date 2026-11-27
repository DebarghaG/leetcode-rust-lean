pub fn shift_grid(grid: &[Vec<i64>], k: i64) -> Vec<Vec<i64>> {
    let m = grid.len();
    let n = grid[0].len();
    let total = m * n;

    let total_i = total as i64;
    let mut kk = k % total_i;
    if kk < 0 {
        kk += total_i;
    }
    let shift = kk as usize;

    let mut out: Vec<Vec<i64>> = Vec::new();

    let mut i = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            let pos = i * n + j;
            let src = (pos + total - shift) % total;
            let si = src / n;
            let sj = src % n;
            row.push(grid[si][sj]);
            j += 1;
        }
        out.push(row);
        i += 1;
    }

    out
}
