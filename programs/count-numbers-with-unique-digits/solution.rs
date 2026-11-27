pub fn count_numbers_with_unique_digits(n: i64) -> i64 {
    let mut total: i64 = 1;
    let mut count: i64 = 9;
    let mut k: i64 = 1;

    while k <= n {
        total += count;
        count = count * (10 - k);
        k += 1;
    }

    total
}
