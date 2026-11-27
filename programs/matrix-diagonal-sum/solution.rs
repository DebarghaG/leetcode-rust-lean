pub fn diagonal_sum(mat: &[Vec<i64>]) -> i64 {
    let n = mat.len();
    if n == 0 {
        return 0;
    }

    let mut sum: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        sum += mat[i][i];

        let j: usize = n - 1 - i;
        if j != i {
            sum += mat[i][j];
        }

        i += 1;
    }

    sum
}
