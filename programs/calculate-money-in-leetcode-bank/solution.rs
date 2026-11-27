pub fn total_money(n: i64) -> i64 {
    let mut total: i64 = 0;
    let mut day: i64 = 0;

    while day < n {
        let week: i64 = day / 7;
        let weekday: i64 = day % 7;
        total = total + week + weekday + 1;
        day = day + 1;
    }

    total
}
