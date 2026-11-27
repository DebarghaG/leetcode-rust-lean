pub fn largest_submatrix(matrix: &[Vec<i64>]) -> i64 {
    let m = matrix.len();
    if m == 0 {
        return 0;
    }

    let n = matrix[0].len();
    if n == 0 {
        return 0;
    }

    let mut heights: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < n {
        heights.push(0);
        j += 1;
    }

    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < m {
        let row = &matrix[i];

        let mut j: usize = 0;
        while j < n {
            if row[j] == 1 {
                heights[j] = heights[j] + 1;
            } else {
                heights[j] = 0;
            }
            j += 1;
        }

        let mut sorted: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < n {
            sorted.push(heights[k]);
            k += 1;
        }

        sorted.sort();

        let mut k: usize = 0;
        let mut width: i64 = n as i64;

        while k < n {
            let area = sorted[k] * width;
            if area > ans {
                ans = area;
            }
            width = width - 1;
            k += 1;
        }

        i += 1;
    }

    ans
}
