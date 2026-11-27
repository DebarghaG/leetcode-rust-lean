pub fn find_peak_grid(mat: &[Vec<i64>]) -> Vec<i64> {
    let m = mat.len();
    let n = mat[0].len();

    let mut lo: usize = 0;
    let mut hi: usize = m - 1;

    while lo < hi {
        let mid: usize = (lo + hi) / 2;
        let row = &mat[mid];

        let mut max_col: usize = 0;
        let mut j: usize = 1;
        while j < n {
            if row[j] > row[max_col] {
                max_col = j;
            }
            j = j + 1;
        }

        let cur = row[max_col];
        if mat[mid + 1][max_col] > cur {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    let last = &mat[lo];
    let mut max_col: usize = 0;
    let mut j: usize = 1;
    while j < n {
        if last[j] > last[max_col] {
            max_col = j;
        }
        j = j + 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    ans.push(lo as i64);
    ans.push(max_col as i64);
    ans
}
