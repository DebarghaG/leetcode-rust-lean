pub fn matrix_block_sum(mat: &[Vec<i64>], k: i64) -> Vec<Vec<i64>> {
    let m = mat.len();
    let n = mat[0].len();

    // 2-D prefix sums with dimensions (m + 1) x (n + 1).
    let mut ps: Vec<Vec<i64>> = Vec::new();

    let mut zero_row: Vec<i64> = Vec::new();
    let mut j = 0;
    while j <= n {
        zero_row.push(0);
        j += 1;
    }
    ps.push(zero_row);

    let mut i = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        row.push(0);

        let mut row_sum: i64 = 0;
        let mut j = 0;
        while j < n {
            row_sum += mat[i][j];
            let value = ps[i][j + 1] + row_sum;
            row.push(value);
            j += 1;
        }

        ps.push(row);
        i += 1;
    }

    let kk = if k <= 0 { 0 } else { k as usize };

    let mut answer: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < m {
        let r1 = if i >= kk { i - kk } else { 0 };
        let r2 = if i + kk < m { i + kk } else { m - 1 };

        let mut out_row: Vec<i64> = Vec::new();

        let mut j = 0;
        while j < n {
            let c1 = if j >= kk { j - kk } else { 0 };
            let c2 = if j + kk < n { j + kk } else { n - 1 };

            let sum = ps[r2 + 1][c2 + 1]
                - ps[r1][c2 + 1]
                - ps[r2 + 1][c1]
                + ps[r1][c1];

            out_row.push(sum);
            j += 1;
        }

        answer.push(out_row);
        i += 1;
    }

    answer
}
