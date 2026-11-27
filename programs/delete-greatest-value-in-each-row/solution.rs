pub fn delete_greatest_value(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }

    let mut rows: Vec<Vec<i64>> = Vec::new();

    let mut i: usize = 0;
    while i < m {
        let src = &grid[i];
        let len = src.len();

        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < len {
            row.push(src[j]);
            j += 1;
        }

        // Sort the row in nondecreasing order using bubble sort.
        let mut a: usize = 0;
        while a < len {
            let mut b: usize = 0;
            while b + 1 < len {
                if row[b] > row[b + 1] {
                    let tmp = row[b];
                    row[b] = row[b + 1];
                    row[b + 1] = tmp;
                }
                b += 1;
            }
            a += 1;
        }

        rows.push(row);
        i += 1;
    }

    let n = rows[0].len();
    let mut answer: i64 = 0;

    let mut c: usize = 0;
    while c < n {
        let mut maximum = rows[0][c];

        let mut r: usize = 1;
        while r < m {
            if rows[r][c] > maximum {
                maximum = rows[r][c];
            }
            r += 1;
        }

        answer += maximum;
        c += 1;
    }

    answer
}
