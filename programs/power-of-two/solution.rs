pub fn is_power_of_two(n: i64) -> bool {
    if n <= 0 {
        return false;
    }

    let mut m = n;
    while m % 2 == 0 {
        m = m / 2;
    }

    m == 1
}
