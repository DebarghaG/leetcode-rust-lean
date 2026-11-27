pub fn find_center(edges: &[Vec<i64>]) -> i64 {
    let a0 = edges[0][0];
    let a1 = edges[0][1];
    let b0 = edges[1][0];
    let b1 = edges[1][1];

    if a0 == b0 || a0 == b1 {
        a0
    } else {
        a1
    }
}
