pub fn row_and_maximum_ones(mat: &[Vec<i64>]) -> Vec<i64> {
    let mut best_idx: i64 = 0;
    let mut best_count: i64 = 0;

    let mut i: usize = 0;
    while i < mat.len() {
        let row = &mat[i];
        let mut count: i64 = 0;
        let mut j: usize = 0;

        while j < row.len() {
            if row[j] == 1 {
                count += 1;
            }
            j += 1;
        }

        if count > best_count {
            best_count = count;
            best_idx = i as i64;
        }

        i += 1;
    }

    let mut result: Vec<i64> = Vec::new();
    result.push(best_idx);
    result.push(best_count);
    result
}
