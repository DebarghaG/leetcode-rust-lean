pub fn restore_matrix(rowSum: &[i64], colSum: &[i64]) -> Vec<Vec<i64>> {
    let n = rowSum.len();
    let m = colSum.len();

    let mut rem_row: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        rem_row.push(rowSum[i]);
        i += 1;
    }

    let mut rem_col: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < m {
        rem_col.push(colSum[j]);
        j += 1;
    }

    let mut out: Vec<Vec<i64>> = Vec::new();
    i = 0;
    while i < n {
        let mut row: Vec<i64> = Vec::new();
        j = 0;
        while j < m {
            let a = rem_row[i];
            let b = rem_col[j];
            let v = if a < b { a } else { b };

            row.push(v);
            rem_row[i] = a - v;
            rem_col[j] = b - v;

            j += 1;
        }
        out.push(row);
        i += 1;
    }

    out
}
