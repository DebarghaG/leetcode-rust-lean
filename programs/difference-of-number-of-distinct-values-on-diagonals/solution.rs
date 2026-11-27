pub fn difference_of_distinct_values(grid: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let m = grid.len();
    let mut ans: Vec<Vec<i64>> = Vec::new();

    if m == 0 {
        return ans;
    }

    let n = grid[0].len();

    let mut r = 0usize;
    while r < m {
        let mut row_ans: Vec<i64> = Vec::new();
        let mut c = 0usize;

        while c < n {
            let mut seen_left: Vec<i64> = Vec::new();
            let mut i = r;
            let mut j = c;

            while i > 0 && j > 0 {
                i -= 1;
                j -= 1;

                let value = grid[i][j];
                let mut found = false;
                let mut k = 0usize;

                while k < seen_left.len() && !found {
                    if seen_left[k] == value {
                        found = true;
                    }
                    k += 1;
                }

                if !found {
                    seen_left.push(value);
                }
            }

            let left_count = seen_left.len() as i64;

            let mut seen_right: Vec<i64> = Vec::new();
            let mut p = r;
            let mut q = c;

            while p + 1 < m && q + 1 < n {
                p += 1;
                q += 1;

                let value = grid[p][q];
                let mut found = false;
                let mut k = 0usize;

                while k < seen_right.len() && !found {
                    if seen_right[k] == value {
                        found = true;
                    }
                    k += 1;
                }

                if !found {
                    seen_right.push(value);
                }
            }

            let right_count = seen_right.len() as i64;
            let mut diff = left_count - right_count;

            if diff < 0 {
                diff = -diff;
            }

            row_ans.push(diff);
            c += 1;
        }

        ans.push(row_ans);
        r += 1;
    }

    ans
}
