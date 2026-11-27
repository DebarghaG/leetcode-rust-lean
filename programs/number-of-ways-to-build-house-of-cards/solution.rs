pub fn house_of_cards(n: i64) -> i64 {
    let n_usize = n as usize;

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= n_usize {
        dp.push(0);
        i += 1;
    }
    dp[0] = 1;

    let mut cards: i64 = 2;
    while cards <= n {
        let c = cards as usize;
        let mut total = n_usize;
        while total >= c {
            dp[total] = dp[total] + dp[total - c];
            total -= 1;
        }
        cards += 3;
    }

    dp[n_usize]
}
