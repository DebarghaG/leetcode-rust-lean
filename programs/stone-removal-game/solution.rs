pub fn can_alice_win(n: i64) -> bool {
    let mut remaining: i64 = n;
    let mut next_removal: i64 = 10;
    let mut successful_moves: i64 = 0;

    while next_removal > 0 && remaining >= next_removal {
        remaining -= next_removal;
        next_removal -= 1;
        successful_moves += 1;
    }

    successful_moves % 2 == 1
}
