pub fn two_egg_drop(n: i64) -> i64 {
    let mut moves: i64 = 0;
    let mut covered: i64 = 0;

    while covered < n {
        moves += 1;
        covered += moves;
    }

    moves
}
