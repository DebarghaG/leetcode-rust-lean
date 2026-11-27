pub fn generate(numRows: i64) -> Vec<Vec<i64>> {
    let mut out: Vec<Vec<i64>> = Vec::new();
    if numRows <= 0 {
        return out;
    }

    let n = numRows as usize;
    let mut r: usize = 0;

    while r < n {
        let len: usize = r + 1;
        let mut row: Vec<i64> = Vec::new();
        let mut c: usize = 0;

        while c < len {
            let mut value: i64 = 1;

            if c > 0 && c + 1 < len {
                value = out[r - 1][c - 1] + out[r - 1][c];
            }

            row.push(value);
            c += 1;
        }

        out.push(row);
        r += 1;
    }

    out
}
