pub fn is_power_of_three(n: i64) -> bool {
    if n <= 0 {
        return false;
    }

    let mut m = n;
    while m % 3 == 0 {
        m = m / 3;
    }

    m == 1
}
