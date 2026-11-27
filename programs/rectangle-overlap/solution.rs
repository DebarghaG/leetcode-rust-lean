pub fn is_rectangle_overlap(rec1: &[i64], rec2: &[i64]) -> bool {
    let x_overlap: bool = rec1[0] < rec2[2] && rec2[0] < rec1[2];
    let y_overlap: bool = rec1[1] < rec2[3] && rec2[1] < rec1[3];
    x_overlap && y_overlap
}
