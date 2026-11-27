pub fn check_powers_of_three(n: i64) -> bool {
    let mut x = n;
    while x > 0 {
        if x % 3 == 2 {
            return false;
        }
        x = x / 3;
    }
    true
}
