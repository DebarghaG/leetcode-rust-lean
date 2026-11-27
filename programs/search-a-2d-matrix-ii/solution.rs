pub fn search_matrix(matrix: &[Vec<i64>], target: i64) -> bool {
    let m = matrix.len();
    let mut found = false;

    let mut valid = false;
    let mut n: usize = 0;
    if m > 0 {
        n = matrix[0].len();
        if n > 0 {
            valid = true;
        }
    }

    if valid {
        let mut row: usize = 0;
        let mut col: usize = n - 1;
        let mut going = true;

        while going && row < m {
            let value = matrix[row][col];
            if value == target {
                found = true;
                going = false;
            } else if value > target {
                if col == 0 {
                    going = false;
                } else {
                    col -= 1;
                }
            } else {
                row += 1;
            }
        }
    }

    found
}
