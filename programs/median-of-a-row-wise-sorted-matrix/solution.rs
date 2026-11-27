pub fn matrix_median(grid: &[Vec<i64>]) -> i64 {
    let m: usize = grid.len();
    let n: usize = grid[0].len();
    let target: usize = (m * n + 1) / 2;

    let mut lo: i64 = 1;
    let mut hi: i64 = 1_000_000;

    while lo < hi {
        let mid: i64 = lo + (hi - lo) / 2;

        let mut count: usize = 0;
        let mut i: usize = 0;

        while i < m {
            let row = &grid[i];

            let mut left: usize = 0;
            let mut right: usize = n;

            while left < right {
                let c: usize = left + (right - left) / 2;
                if row[c] <= mid {
                    left = c + 1;
                } else {
                    right = c;
                }
            }

            count += left;
            i += 1;
        }

        if count >= target {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo
}
