pub fn number_of_cuts(n: i64) -> i64 {
    if n == 1 {
        0
    } else if n % 2 == 0 {
        n / 2
    } else {
        n
    }
}
