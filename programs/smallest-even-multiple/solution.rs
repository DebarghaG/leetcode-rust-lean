pub fn smallest_even_multiple(n: i64) -> i64 {
    if n % 2 == 0 {
        n
    } else {
        n * 2
    }
}
