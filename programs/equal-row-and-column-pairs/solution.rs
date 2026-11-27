pub fn equal_pairs(grid: &[Vec<i64>]) -> i64 {
    let n = grid.len();
    let mut count: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let mut j: usize = 0;
        while j < n {
            let mut equal: bool = true;
            let mut k: usize = 0;

            while k < n {
                if grid[i][k] != grid[k][j] {
                    equal = false;
                    k = n;
                } else {
                    k += 1;
                }
            }

            if equal {
                count += 1;
            }

            j += 1;
        }

        i += 1;
    }

    count
}
