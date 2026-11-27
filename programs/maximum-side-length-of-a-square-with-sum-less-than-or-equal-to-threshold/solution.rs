pub fn max_side_length(mat: &[Vec<i64>], threshold: i64) -> i64 {
    let m = mat.len();
    if m == 0 {
        return 0;
    }
    let n = mat[0].len();
    if n == 0 {
        return 0;
    }

    let mut prefix: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i <= m {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j <= n {
            row.push(0);
            j += 1;
        }
        prefix.push(row);
        i += 1;
    }

    i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            let val = mat[i][j];
            let top = prefix[i][j + 1];
            let left = prefix[i + 1][j];
            let diag = prefix[i][j];
            prefix[i + 1][j + 1] = val + top + left - diag;
            j += 1;
        }
        i += 1;
    }

    let mut max_possible = m;
    if n < max_possible {
        max_possible = n;
    }

    let mut low: usize = 0;
    let mut high: usize = max_possible + 1;

    while low + 1 < high {
        let mid = (low + high) / 2;
        let ok = square_exists(&prefix, m, n, mid, threshold);
        if ok {
            low = mid;
        } else {
            high = mid;
        }
    }

    low as i64
}

fn square_exists(
    prefix: &[Vec<i64>],
    m: usize,
    n: usize,
    side: usize,
    threshold: i64,
) -> bool {
    let mut found = false;
    if side == 0 {
        found = true;
    } else if side > m || side > n {
        found = false;
    } else {
        let mut i = 0;
        while i + side <= m && !found {
            let mut j = 0;
            while j + side <= n && !found {
                let sum = prefix[i + side][j + side]
                    - prefix[i][j + side]
                    - prefix[i + side][j]
                    + prefix[i][j];
                if sum <= threshold {
                    found = true;
                }
                j += 1;
            }
            i += 1;
        }
    }

    found
}
