pub fn furthest_distance_from_origin(moves: &[u8]) -> i64 {
    let mut left: i64 = 0;
    let mut right: i64 = 0;
    let mut underscores: i64 = 0;

    let mut i: usize = 0;
    while i < moves.len() {
        let c = moves[i];
        if c == b'L' {
            left += 1;
        } else if c == b'R' {
            right += 1;
        } else {
            underscores += 1;
        }
        i += 1;
    }

    let diff = right - left;
    let abs_diff = if diff < 0 { -diff } else { diff };

    abs_diff + underscores
}
