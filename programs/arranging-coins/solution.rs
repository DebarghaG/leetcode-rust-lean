pub fn arrange_coins(n: i64) -> i64 {
    let mut rows: i64 = 0;
    let mut remaining: i64 = n;

    while rows + 1 <= remaining {
        rows += 1;
        remaining -= rows;
    }

    rows
}
