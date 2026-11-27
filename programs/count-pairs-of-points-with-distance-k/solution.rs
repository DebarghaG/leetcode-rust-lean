pub fn count_pairs(coordinates: &[Vec<i64>], k: i64) -> i64 {
    let n = coordinates.len();
    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let x1 = coordinates[i][0];
        let y1 = coordinates[i][1];
        let mut j: usize = i + 1;
        while j < n {
            let x2 = coordinates[j][0];
            let y2 = coordinates[j][1];
            let d = (x1 ^ x2) + (y1 ^ y2);
            if d == k {
                total = total + 1;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    total
}
