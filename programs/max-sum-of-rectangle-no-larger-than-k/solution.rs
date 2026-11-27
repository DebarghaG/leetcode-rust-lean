pub fn max_sum_submatrix(matrix: &[Vec<i64>], k: i64) -> i64 {
    let rows = matrix.len();
    if rows == 0 {
        return 0;
    }
    let cols = matrix[0].len();

    let mut ans: i64 = -1_000_000_000;
    let mut top: usize = 0;

    while top < rows {
        let mut col_sums: Vec<i64> = Vec::new();
        let mut c: usize = 0;
        while c < cols {
            col_sums.push(0);
            c += 1;
        }

        let mut bottom: usize = top;
        while bottom < rows {
            let row = &matrix[bottom];

            let mut j: usize = 0;
            while j < cols {
                col_sums[j] += row[j];
                j += 1;
            }

            let mut left: usize = 0;
            while left < cols {
                let mut sum: i64 = 0;
                let mut right: usize = left;

                while right < cols {
                    sum += col_sums[right];
                    if sum <= k && sum > ans {
                        ans = sum;
                    }
                    right += 1;
                }

                left += 1;
            }

            bottom += 1;
        }

        top += 1;
    }

    ans
}
