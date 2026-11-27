fn count_leq(matrix: &[Vec<i64>], x: i64) -> i64 {
    let n = matrix.len();
    if n == 0 {
        return 0;
    }

    let mut row = n;
    let mut col = 0usize;
    let mut count: i64 = 0;

    while row > 0 && col < n {
        if matrix[row - 1][col] <= x {
            count += row as i64;
            col += 1;
        } else {
            row -= 1;
        }
    }

    count
}

pub fn kth_smallest(matrix: &[Vec<i64>], k: i64) -> i64 {
    let n = matrix.len();
    if n == 0 {
        return 0;
    }

    let mut low = matrix[0][0];
    let mut high = matrix[n - 1][n - 1];

    while low < high {
        let mid = low + (high - low) / 2;
        let count = count_leq(matrix, mid);

        if count >= k {
            high = mid;
        } else {
            low = mid + 1;
        }
    }

    low
}
