pub fn max_matrix_sum(matrix: &[Vec<i64>]) -> i64 {
    let first = matrix[0][0];
    let mut min_abs: i64 = if first < 0 { -first } else { first };

    let mut total: i64 = 0;
    let mut odd_negatives: bool = false;

    let n = matrix.len();
    let mut i = 0;
    while i < n {
        let row = &matrix[i];
        let m = row.len();
        let mut j = 0;
        while j < m {
            let x = row[j];
            let a = if x < 0 { -x } else { x };
            total += a;

            if x < 0 {
                odd_negatives = !odd_negatives;
            }

            if a < min_abs {
                min_abs = a;
            }

            j += 1;
        }
        i += 1;
    }

    if odd_negatives {
        total - 2 * min_abs
    } else {
        total
    }
}
