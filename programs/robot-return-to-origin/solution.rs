pub fn judge_circle(moves: &[u8]) -> bool {
    let mut x: i64 = 0;
    let mut y: i64 = 0;
    let n = moves.len();
    let mut i: usize = 0;
    while i < n {
        let c = moves[i];
        if c == b'R' {
            x = x + 1;
        } else if c == b'L' {
            x = x - 1;
        } else if c == b'U' {
            y = y + 1;
        } else if c == b'D' {
            y = y - 1;
        }
        i = i + 1;
    }
    x == 0 && y == 0
}
