pub fn is_toeplitz_matrix(matrix: &[Vec<i64>]) -> bool {
    let m = matrix.len();
    if m == 0 {
        return true;
    }

    let n = matrix[0].len();

    let mut ok: bool = true;
    let mut i: usize = 1;

    while i < m {
        let mut j: usize = 1;
        while j < n {
            if matrix[i][j] != matrix[i - 1][j - 1] {
                ok = false;
            }
            j += 1;
        }
        i += 1;
    }

    ok
}
