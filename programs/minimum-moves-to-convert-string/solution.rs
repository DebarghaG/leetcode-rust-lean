pub fn minimum_moves(s: &[u8]) -> i64 {
    let n = s.len();
    let mut moves: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        if s[i] == b'X' {
            moves += 1;
            i += 3;
        } else {
            i += 1;
        }
    }

    moves
}
