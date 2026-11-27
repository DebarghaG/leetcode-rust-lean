fn ways3(m: i64) -> i64 {
    if m < 0 {
        0
    } else {
        (m + 2) * (m + 1) / 2
    }
}

pub fn distribute_candies(n: i64, limit: i64) -> i64 {
    let a = ways3(n);
    let b = ways3(n - (limit + 1));
    let c = ways3(n - 2 * (limit + 1));
    let d = ways3(n - 3 * (limit + 1));

    a - 3 * b + 3 * c - d
}
