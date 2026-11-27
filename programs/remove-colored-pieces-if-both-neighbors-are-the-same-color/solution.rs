pub fn winner_of_game(colors: &[u8]) -> bool {
    let n = colors.len();
    let mut alice_moves: i64 = 0;
    let mut bob_moves: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let c = colors[i];
        let mut j = i;
        while j < n && colors[j] == c {
            j += 1;
        }

        let len = (j - i) as i64;
        if len >= 3 {
            if c == b'A' {
                alice_moves += len - 2;
            } else {
                bob_moves += len - 2;
            }
        }

        i = j;
    }

    alice_moves > bob_moves
}
