pub fn count_negatives(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }

    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let mut i: usize = m - 1;
    let mut j: usize = 0;
    let mut count: i64 = 0;
    let mut done: bool = false;

    while !done {
        let row = &grid[i];

        if row[j] < 0 {
            // Since the matrix is non-increasing row-wise, everything at
            // or to the right of column j in this row is negative.
            count = count + (n - j) as i64;

            if i == 0 {
                done = true;
            } else {
                i = i - 1;
            }
        } else {
            // This cell is non-negative; the negative suffix in this row
            // must start further right.
            j = j + 1;
            if j >= n {
                done = true;
            }
        }
    }

    count
}
