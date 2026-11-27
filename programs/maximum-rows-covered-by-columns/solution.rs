pub fn maximum_rows(matrix: &[Vec<i64>], numSelect: i64) -> i64 {
    let m = matrix.len();
    if m == 0 {
        return 0;
    }

    let n = matrix[0].len();

    let mut total: i64 = 1;
    let mut t: usize = 0;
    while t < n {
        total = total * 2;
        t += 1;
    }

    let mut best: i64 = 0;
    let mut mask: i64 = 0;

    while mask < total {
        let mut selected_count: i64 = 0;
        let mut j: usize = 0;

        while j < n {
            let bit: i64 = (mask >> j) & 1_i64;
            selected_count += bit;
            j += 1;
        }

        if selected_count == numSelect {
            let mut covered: i64 = 0;
            let mut i: usize = 0;

            while i < m {
                let row = &matrix[i];
                let mut ok: bool = true;
                let mut col: usize = 0;

                while col < n {
                    if row[col] == 1_i64 {
                        if (mask & (1_i64 << col)) == 0_i64 {
                            ok = false;
                        }
                    }
                    col += 1;
                }

                if ok {
                    covered += 1;
                }

                i += 1;
            }

            if covered > best {
                best = covered;
            }
        }

        mask += 1;
    }

    best
}
