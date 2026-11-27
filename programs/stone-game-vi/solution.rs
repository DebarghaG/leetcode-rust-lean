pub fn stone_game_vi(alice_values: &[i64], bob_values: &[i64]) -> i64 {
    let n = alice_values.len();
    let mut diff: i64 = 0;
    let mut turn: i64 = 0;
    let mut wanted_sum: i64 = 200;

    while wanted_sum >= 2 {
        let mut i: usize = 0;
        while i < n {
            if alice_values[i] + bob_values[i] == wanted_sum {
                if turn == 0 {
                    diff += alice_values[i];
                } else {
                    diff -= bob_values[i];
                }
                turn = 1 - turn;
            }
            i += 1;
        }
        wanted_sum -= 1;
    }

    if diff > 0 {
        1
    } else if diff < 0 {
        -1
    } else {
        0
    }
}
