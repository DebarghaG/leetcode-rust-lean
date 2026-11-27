pub fn check_two_chessboards(coordinate1: &[u8], coordinate2: &[u8]) -> bool {
    let col1 = coordinate1[0] as i64;
    let row1 = coordinate1[1] as i64;
    let col2 = coordinate2[0] as i64;
    let row2 = coordinate2[1] as i64;

    ((col1 + row1) % 2) == ((col2 + row2) % 2)
}
