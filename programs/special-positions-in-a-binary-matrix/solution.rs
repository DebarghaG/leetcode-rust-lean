pub fn num_special(mat: &[Vec<i64>]) -> i64 {
    let m = mat.len();
    if m == 0 {
        return 0;
    }

    let n = mat[0].len();

    let mut row_counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < m {
        row_counts.push(0);
        i = i + 1;
    }

    let mut col_counts: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < n {
        col_counts.push(0);
        j = j + 1;
    }

    i = 0;
    while i < m {
        j = 0;
        while j < n {
            let value = mat[i][j];
            if value == 1 {
                row_counts[i] = row_counts[i] + 1;
                col_counts[j] = col_counts[j] + 1;
            }
            j = j + 1;
        }
        i = i + 1;
    }

    let mut ans: i64 = 0;
    i = 0;
    while i < m {
        j = 0;
        while j < n {
            if mat[i][j] == 1 && row_counts[i] == 1 && col_counts[j] == 1 {
                ans = ans + 1;
            }
            j = j + 1;
        }
        i = i + 1;
    }

    ans
}
