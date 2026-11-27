pub fn spiral_matrix_iii(rows: i64, cols: i64, rStart: i64, cStart: i64) -> Vec<Vec<i64>> {
    let total: i64 = rows * cols;
    let mut out: Vec<Vec<i64>> = Vec::new();

    let mut r: i64 = rStart;
    let mut c: i64 = cStart;

    let mut first: Vec<i64> = Vec::new();
    first.push(r);
    first.push(c);
    out.push(first);
    let mut count: i64 = 1;

    if count >= total {
        return out;
    }

    let bound: i64 = 2 * (rows + cols) + 10;
    let mut step_len: i64 = 1;
    let mut dir: i64 = 0;

    while step_len <= bound {
        let mut twice: i64 = 0;

        while twice < 2 {
            let mut k: i64 = 0;

            while k < step_len {
                if dir == 0 {
                    c = c + 1;
                } else if dir == 1 {
                    r = r + 1;
                } else if dir == 2 {
                    c = c - 1;
                } else {
                    r = r - 1;
                }

                if count < total && r >= 0 && r < rows && c >= 0 && c < cols {
                    let mut cell: Vec<i64> = Vec::new();
                    cell.push(r);
                    cell.push(c);
                    out.push(cell);
                    count = count + 1;
                }

                k = k + 1;
            }

            if dir == 3 {
                dir = 0;
            } else {
                dir = dir + 1;
            }

            twice = twice + 1;
        }

        step_len = step_len + 1;
    }

    out
}
