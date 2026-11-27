pub fn min_moves(target: i64, maxDoubles: i64) -> i64 {
    let mut x = target;
    let mut doubles = maxDoubles;
    let mut moves = 0i64;

    while x > 1 && doubles > 0 {
        if x % 2 == 1 {
            x -= 1;
            moves += 1;
        }

        if x > 1 && doubles > 0 {
            x /= 2;
            moves += 1;
            doubles -= 1;
        }
    }

    moves += x - 1;
    moves
}
