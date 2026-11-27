fn min_line_swaps(count_ones: i64, mismatch0: i64, n: i64) -> i64 {
    if n % 2 == 0 {
        let half = n / 2;
        if count_ones != half {
            return -1;
        }

        let mut best_mismatch = mismatch0;
        let other = n - mismatch0;
        if other < best_mismatch {
            best_mismatch = other;
        }
        best_mismatch / 2
    } else {
        let low = n / 2;
        let high = n - low;

        if count_ones == low {
            mismatch0 / 2
        } else if count_ones == high {
            (n - mismatch0) / 2
        } else {
            -1
        }
    }
}

pub fn moves_to_chessboard(board: &[Vec<i64>]) -> i64 {
    let n_usize = board.len();
    if n_usize == 0 {
        return -1;
    }

    let n = n_usize as i64;
    let base = board[0][0];

    // Verify structural constraint without early returns inside loops.
    let mut valid = true;
    for i in 0..n_usize {
        for j in 0..n_usize {
            let same_as_row_start = board[i][j] == board[i][0];
            let same_as_top = board[0][j] == base;
            if same_as_row_start != same_as_top {
                valid = false;
            }
        }
    }

    if !valid {
        return -1;
    }

    let mut row_ones: i64 = 0;
    let mut row_mismatch: i64 = 0;

    for i in 0..n_usize {
        let label: i64 = if board[i][0] != base { 1 } else { 0 };
        if label == 1 {
            row_ones += 1;
        }

        let target: i64 = if i % 2 == 0 { 0 } else { 1 };
        if label != target {
            row_mismatch += 1;
        }
    }

    let mut col_ones: i64 = 0;
    let mut col_mismatch: i64 = 0;

    for j in 0..n_usize {
        let label: i64 = if board[0][j] != base { 1 } else { 0 };
        if label == 1 {
            col_ones += 1;
        }

        let target: i64 = if j % 2 == 0 { 0 } else { 1 };
        if label != target {
            col_mismatch += 1;
        }
    }

    let row_cost = min_line_swaps(row_ones, row_mismatch, n);
    if row_cost < 0 {
        return -1;
    }

    let col_cost = min_line_swaps(col_ones, col_mismatch, n);
    if col_cost < 0 {
        return -1;
    }

    row_cost + col_cost
}
