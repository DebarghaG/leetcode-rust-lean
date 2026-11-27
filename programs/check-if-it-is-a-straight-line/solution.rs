pub fn check_straight_line(coordinates: &[Vec<i64>]) -> bool {
    let n = coordinates.len();
    if n <= 2 {
        return true;
    }

    let x0 = coordinates[0][0];
    let y0 = coordinates[0][1];
    let x1 = coordinates[1][0];
    let y1 = coordinates[1][1];

    let dx = x1 - x0;
    let dy = y1 - y0;

    let mut i = 2;
    while i < n {
        let xi = coordinates[i][0];
        let yi = coordinates[i][1];

        // Cross product: (xi - x0) * dy - (yi - y0) * dx == 0
        let cross = (xi - x0) * dy - (yi - y0) * dx;
        if cross != 0 {
            return false;
        }

        i += 1;
    }

    true
}
