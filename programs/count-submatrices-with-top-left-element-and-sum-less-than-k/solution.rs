pub fn count_submatrices(grid: &[Vec<i64>], k: i64) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }

    let n = grid[0].len();
    let mut col_sum: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < n {
        col_sum.push(0);
        j += 1;
    }

    let mut ans: i64 = 0;
    let mut i = 0;
    while i < m {
        let row = &grid[i];
        let mut running: i64 = 0;
        let mut j = 0;
        while j < n {
            col_sum[j] = col_sum[j] + row[j];
            running = running + col_sum[j];
            if running <= k {
                ans += 1;
            }
            j += 1;
        }
        i += 1;
    }

    ans
}
