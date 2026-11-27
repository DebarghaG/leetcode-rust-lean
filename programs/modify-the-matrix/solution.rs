pub fn modified_matrix(matrix: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let m = matrix.len();
    if m == 0 {
        return Vec::new();
    }

    let n = matrix[0].len();

    let mut col_max: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < n {
        let mut mx: i64 = -1;
        let mut i = 0;
        while i < m {
            let v = matrix[i][j];
            if v > mx {
                mx = v;
            }
            i += 1;
        }
        col_max.push(mx);
        j += 1;
    }

    let mut answer: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            let v = matrix[i][j];
            if v == -1 {
                row.push(col_max[j]);
            } else {
                row.push(v);
            }
            j += 1;
        }
        answer.push(row);
        i += 1;
    }

    answer
}
