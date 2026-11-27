pub fn add_digits(num: i64) -> i64 {
    if num == 0 {
        0
    } else {
        1 + (num - 1) % 9
    }
}
