pub fn num_submat(mat: &[Vec<i64>]) -> i64 {
    let m = mat.len();
    if m == 0 {
        return 0;
    }

    let n = mat[0].len();
    let mut heights: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < n {
        heights.push(0);
        j += 1;
    }

    let mut total: i64 = 0;
    let mut i = 0;
    while i < m {
        let mut c = 0;
        while c < n {
            if mat[i][c] == 1 {
                let h = heights[c];
                heights[c] = h + 1;
            } else {
                heights[c] = 0;
            }
            c += 1;
        }

        let mut left = 0;
        while left < n {
            let mut min_height = heights[left];
            let mut right = left;
            while right < n {
                if heights[right] < min_height {
                    min_height = heights[right];
                }
                total = total + min_height;
                right += 1;
            }
            left += 1;
        }

        i += 1;
    }

    total
}
