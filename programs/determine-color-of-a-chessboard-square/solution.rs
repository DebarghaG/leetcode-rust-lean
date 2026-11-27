pub fn square_is_white(coordinates: &[u8]) -> bool {
    let col: i64 = (coordinates[0] - b'a') as i64;
    let row: i64 = (coordinates[1] - b'1') as i64;
    let sum: i64 = col + row;
    sum % 2 != 0
}
