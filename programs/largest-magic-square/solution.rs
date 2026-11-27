pub fn largest_magic_square(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }

    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let mut max_k = m;
    if n < max_k {
        max_k = n;
    }

    let mut result: i64 = 1;
    let mut found = false;
    let mut k = max_k;

    while k > 0 && !found {
        let mut top = 0usize;
        while top + k <= m && !found {
            let mut left = 0usize;
            while left + k <= n && !found {
                if is_magic_square(grid, top, left, k) {
                    result = k as i64;
                    found = true;
                }
                left += 1;
            }
            top += 1;
        }
        k -= 1;
    }

    result
}

fn is_magic_square(grid: &[Vec<i64>], top: usize, left: usize, k: usize) -> bool {
    let mut target: i64 = 0;
    let mut j: usize = 0;
    while j < k {
        target += grid[top][left + j];
        j += 1;
    }

    let mut ok = true;

    let mut i: usize = 0;
    while i < k {
        let mut row_sum: i64 = 0;
        let mut jj: usize = 0;
        while jj < k {
            row_sum += grid[top + i][left + jj];
            jj += 1;
        }
        if row_sum != target {
            ok = false;
        }
        i += 1;
    }

    let mut c: usize = 0;
    while c < k {
        let mut col_sum: i64 = 0;
        let mut ii: usize = 0;
        while ii < k {
            col_sum += grid[top + ii][left + c];
            ii += 1;
        }
        if col_sum != target {
            ok = false;
        }
        c += 1;
    }

    let mut diag1: i64 = 0;
    let mut d: usize = 0;
    while d < k {
        diag1 += grid[top + d][left + d];
        d += 1;
    }
    if diag1 != target {
        ok = false;
    }

    let mut diag2: i64 = 0;
    let mut e: usize = 0;
    while e < k {
        diag2 += grid[top + e][left + (k - 1 - e)];
        e += 1;
    }
    if diag2 != target {
        ok = false;
    }

    ok
}
