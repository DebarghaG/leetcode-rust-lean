pub fn get_biggest_three(grid: &[Vec<i64>]) -> Vec<i64> {
    let m = grid.len();
    if m == 0 {
        return Vec::new();
    }
    let n = grid[0].len();
    if n == 0 {
        return Vec::new();
    }

    let mut top0: i64 = -1;
    let mut top1: i64 = -1;
    let mut top2: i64 = -1;

    let mut i: usize = 0;
    while i < m {
        let mut j: usize = 0;
        while j < n {
            // Area 0 rhombus: just the cell itself.
            let center_sum = grid[i][j];
            if center_sum != top0 && center_sum != top1 && center_sum != top2 {
                if center_sum > top0 {
                    top2 = top1;
                    top1 = top0;
                    top0 = center_sum;
                } else if center_sum > top1 {
                    top2 = top1;
                    top1 = center_sum;
                } else if center_sum > top2 {
                    top2 = center_sum;
                }
            }

            // Larger rhombi centered at (i, j).
            let mut r: usize = 1;
            while i >= r && j >= r && i + r < m && j + r < n {
                let mut sum: i64 = 0;
                let mut k: usize = 0;

                while k < r {
                    // Top to right side.
                    sum += grid[i - r + k][j + k];

                    // Right to bottom side.
                    sum += grid[i + k][j + r - k];

                    // Bottom to left side.
                    sum += grid[i + r - k][j - k];

                    // Left to top side.
                    sum += grid[i - k][j - r + k];

                    k += 1;
                }

                if sum != top0 && sum != top1 && sum != top2 {
                    if sum > top0 {
                        top2 = top1;
                        top1 = top0;
                        top0 = sum;
                    } else if sum > top1 {
                        top2 = top1;
                        top1 = sum;
                    } else if sum > top2 {
                        top2 = sum;
                    }
                }

                r += 1;
            }

            j += 1;
        }
        i += 1;
    }

    let mut result: Vec<i64> = Vec::new();
    if top0 >= 0 {
        result.push(top0);
    }
    if top1 >= 0 {
        result.push(top1);
    }
    if top2 >= 0 {
        result.push(top2);
    }

    result
}
