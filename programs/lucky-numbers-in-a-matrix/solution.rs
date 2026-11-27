pub fn lucky_numbers(matrix: &[Vec<i64>]) -> Vec<i64> {
    let m = matrix.len();
    if m == 0 {
        return Vec::new();
    }

    let n = matrix[0].len();
    if n == 0 {
        return Vec::new();
    }

    let mut row_min: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < m {
        let row = &matrix[i];
        let mut mn = row[0];
        let mut j = 1;
        while j < n {
            if row[j] < mn {
                mn = row[j];
            }
            j += 1;
        }
        row_min.push(mn);
        i += 1;
    }

    let mut col_max: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < n {
        let mut mx = matrix[0][j];
        let mut i = 1;
        while i < m {
            if matrix[i][j] > mx {
                mx = matrix[i][j];
            }
            i += 1;
        }
        col_max.push(mx);
        j += 1;
    }

    let mut out: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            let v = matrix[i][j];
            if v == row_min[i] && v == col_max[j] {
                out.push(v);
            }
            j += 1;
        }
        i += 1;
    }

    out
}
