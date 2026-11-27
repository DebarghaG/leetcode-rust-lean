pub fn matrix_sum_queries(n: i64, queries: &[Vec<i64>]) -> i64 {
    let n_usize = n as usize;

    let mut seen_rows: Vec<bool> = Vec::new();
    let mut seen_cols: Vec<bool> = Vec::new();

    let mut i = 0;
    while i < n_usize {
        seen_rows.push(false);
        seen_cols.push(false);
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut rows_used: i64 = 0;
    let mut cols_used: i64 = 0;

    let mut pos = queries.len();
    while pos > 0 {
        pos -= 1;

        let typ = queries[pos][0];
        let idx = queries[pos][1] as usize;
        let val = queries[pos][2];

        if typ == 0 {
            if !seen_rows[idx] {
                seen_rows[idx] = true;
                ans += val * (n - cols_used);
                rows_used += 1;
            }
        } else {
            if !seen_cols[idx] {
                seen_cols[idx] = true;
                ans += val * (n - rows_used);
                cols_used += 1;
            }
        }
    }

    ans
}
