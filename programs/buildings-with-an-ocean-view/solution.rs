pub fn find_buildings(heights: &[i64]) -> Vec<i64> {
    let n = heights.len();
    if n == 0 {
        return Vec::new();
    }

    let mut rev_indices: Vec<i64> = Vec::new();
    let mut max_right: i64 = -1;

    let mut i = n;
    while i > 0 {
        i -= 1;
        let h = heights[i];
        if h > max_right {
            rev_indices.push(i as i64);
            max_right = h;
        }
    }

    let mut result: Vec<i64> = Vec::new();
    let m = rev_indices.len();
    let mut k = 0;
    while k < m {
        result.push(rev_indices[m - 1 - k]);
        k += 1;
    }

    result
}
