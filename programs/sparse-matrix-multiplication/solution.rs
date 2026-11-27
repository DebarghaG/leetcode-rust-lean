pub fn multiply(mat1: &[Vec<i64>], mat2: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let m = mat1.len();
    if m == 0 {
        return Vec::new();
    }

    let k = mat1[0].len();
    let n = mat2[0].len();

    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;

    while i < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;

        while j < n {
            let mut sum: i64 = 0;
            let mut p = 0;

            while p < k {
                sum = sum + mat1[i][p] * mat2[p][j];
                p += 1;
            }

            row.push(sum);
            j += 1;
        }

        out.push(row);
        i += 1;
    }

    out
}
