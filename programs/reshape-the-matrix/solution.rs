pub fn matrix_reshape(mat: &[Vec<i64>], r: i64, c: i64) -> Vec<Vec<i64>> {
    let m = mat.len();
    let n = mat[0].len();

    let total: i64 = (m as i64) * (n as i64);
    let target: i64 = r * c;

    if total != target {
        let mut out: Vec<Vec<i64>> = Vec::new();
        let mut i = 0;
        while i < m {
            let row = &mat[i];
            let mut new_row: Vec<i64> = Vec::new();
            let mut j = 0;
            while j < n {
                new_row.push(row[j]);
                j += 1;
            }
            out.push(new_row);
            i += 1;
        }
        return out;
    }

    let rr = r as usize;
    let cc = c as usize;

    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < rr {
        let mut new_row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < cc {
            let flat = i * cc + j;
            let src_row = flat / n;
            let src_col = flat % n;
            new_row.push(mat[src_row][src_col]);
            j += 1;
        }
        out.push(new_row);
        i += 1;
    }

    out
}
