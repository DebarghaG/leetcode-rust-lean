pub fn smallest_number(n: i64) -> i64 {
    let mut x: i64 = 1;
    while x < n {
        x = x * 2 + 1;
    }
    x
}
