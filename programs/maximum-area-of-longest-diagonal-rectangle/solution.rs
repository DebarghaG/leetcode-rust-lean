pub fn area_of_max_diagonal(dimensions: &[Vec<i64>]) -> i64 {
    let n = dimensions.len();
    let mut best_diag_sq: i64 = -1;
    let mut best_area: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let row = &dimensions[i];
        let length = row[0];
        let width = row[1];

        let diag_sq = length * length + width * width;
        let area = length * width;

        if diag_sq > best_diag_sq || (diag_sq == best_diag_sq && area > best_area) {
            best_diag_sq = diag_sq;
            best_area = area;
        }

        i += 1;
    }

    best_area
}
