pub fn generate_matrix(n: i64) -> Vec<Vec<i64>> {
    let n_usize = n as usize;

    let mut matrix: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < n_usize {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n_usize {
            row.push(0);
            j += 1;
        }
        matrix.push(row);
        i += 1;
    }

    let mut top: usize = 0;
    let mut bottom: usize = n_usize;
    let mut left: usize = 0;
    let mut right: usize = n_usize;
    let mut val: i64 = 1;

    while top < bottom && left < right {
        let mut j = left;
        while j < right {
            matrix[top][j] = val;
            val += 1;
            j += 1;
        }
        top += 1;

        let mut r = top;
        while r < bottom {
            matrix[r][right - 1] = val;
            val += 1;
            r += 1;
        }
        right -= 1;

        if top < bottom {
            let mut c = right;
            while c > left {
                c -= 1;
                matrix[bottom - 1][c] = val;
                val += 1;
            }
            bottom -= 1;
        }

        if left < right {
            let mut r2 = bottom;
            while r2 > top {
                r2 -= 1;
                matrix[r2][left] = val;
                val += 1;
            }
            left += 1;
        }
    }

    matrix
}
