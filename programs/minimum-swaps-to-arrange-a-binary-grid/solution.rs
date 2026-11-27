pub fn min_swaps(grid: &[Vec<i64>]) -> i64 {
    let n: usize = grid.len();

    let mut trailing: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < n {
        let mut cnt: i64 = 0;
        let mut k: usize = n;
        let mut still_zero: bool = true;

        while k > 0 {
            k -= 1;
            if still_zero {
                if grid[i][k] == 0 {
                    cnt += 1;
                } else {
                    still_zero = false;
                }
            }
        }

        trailing.push(cnt);
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut pos: usize = 0;

    while pos < n {
        let req: i64 = (n as i64) - 1 - (pos as i64);

        let mut j: usize = pos;
        let mut found: bool = false;

        while j < n && !found {
            if trailing[j] >= req {
                found = true;
            } else {
                j += 1;
            }
        }

        if !found {
            return -1;
        }

        ans += (j - pos) as i64;

        let mut k: usize = j;
        while k > pos {
            let tmp: i64 = trailing[k];
            trailing[k] = trailing[k - 1];
            trailing[k - 1] = tmp;
            k -= 1;
        }

        pos += 1;
    }

    ans
}
