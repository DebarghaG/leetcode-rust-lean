pub fn num_magic_squares_inside(grid: &[Vec<i64>]) -> i64 {
    let rows = grid.len();
    if rows < 3 {
        return 0;
    }

    let cols = grid[0].len();
    if cols < 3 {
        return 0;
    }

    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i + 2 < rows {
        let mut j: usize = 0;

        while j + 2 < cols {
            if is_magic_square(grid, i, j) {
                ans += 1;
            }
            j += 1;
        }

        i += 1;
    }

    ans
}

fn is_magic_square(grid: &[Vec<i64>], r: usize, c: usize) -> bool {
    let mut vals: Vec<i64> = Vec::new();

    let mut dr: usize = 0;
    while dr < 3 {
        let mut dc: usize = 0;
        while dc < 3 {
            vals.push(grid[r + dr][c + dc]);
            dc += 1;
        }
        dr += 1;
    }

    // Check range [1,9] and distinctness without early returns.
    let mut ok = true;

    let mut m: usize = 0;
    while m < 9 {
        let v = vals[m];
        if v < 1 || v > 9 {
            ok = false;
        }
        let mut p: usize = 0;
        while p < m {
            if vals[p] == v {
                ok = false;
            }
            p += 1;
        }
        m += 1;
    }

    if ok {
        let s = vals[0] + vals[1] + vals[2];

        if vals[3] + vals[4] + vals[5] != s {
            ok = false;
        }
        if vals[6] + vals[7] + vals[8] != s {
            ok = false;
        }
        if vals[0] + vals[3] + vals[6] != s {
            ok = false;
        }
        if vals[1] + vals[4] + vals[7] != s {
            ok = false;
        }
        if vals[2] + vals[5] + vals[8] != s {
            ok = false;
        }
        if vals[0] + vals[4] + vals[8] != s {
            ok = false;
        }
        if vals[2] + vals[4] + vals[6] != s {
            ok = false;
        }
    }

    ok
}
