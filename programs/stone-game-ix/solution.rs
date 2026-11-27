pub fn stone_game_ix(stones: &[i64]) -> bool {
    let mut c0: i64 = 0;
    let mut c1: i64 = 0;
    let mut c2: i64 = 0;

    let n = stones.len();
    let mut i: usize = 0;
    while i < n {
        let r = stones[i] % 3;
        if r == 0 {
            c0 += 1;
        } else if r == 1 {
            c1 += 1;
        } else {
            c2 += 1;
        }
        i += 1;
    }

    if c1 == 0 && c2 == 0 {
        return false;
    }

    if c0 % 2 == 0 {
        return c1 > 0 && c2 > 0;
    }

    let diff = if c1 > c2 { c1 - c2 } else { c2 - c1 };
    diff > 2
}
