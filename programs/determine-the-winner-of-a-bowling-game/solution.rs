fn score(player: &[i64]) -> i64 {
    let n = player.len();
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut value: i64 = player[i];

        if i >= 1 && player[i - 1] == 10 {
            value = value * 2;
        } else if i >= 2 && player[i - 2] == 10 {
            value = value * 2;
        }

        total = total + value;
        i = i + 1;
    }

    total
}

pub fn is_winner(player1: &[i64], player2: &[i64]) -> i64 {
    let score1: i64 = score(player1);
    let score2: i64 = score(player2);

    if score1 > score2 {
        1
    } else if score2 > score1 {
        2
    } else {
        0
    }
}
