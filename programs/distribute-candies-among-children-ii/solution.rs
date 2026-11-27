fn choose2(m: i64) -> i64 {
    if m < 2 {
        0
    } else {
        m * (m - 1) / 2
    }
}

pub fn distribute_candies(n: i64, limit: i64) -> i64 {
    let step = limit + 1;
    let total = choose2(n + 2);
    let over1 = choose2(n + 2 - step);
    let over2 = choose2(n + 2 - 2 * step);
    let over3 = choose2(n + 2 - 3 * step);

    total - 3 * over1 + 3 * over2 - over3
}
