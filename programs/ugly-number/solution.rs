pub fn is_ugly(n: i64) -> bool {
    if n <= 0 {
        return false;
    }

    let mut x = n;

    while x % 2 == 0 {
        x = x / 2;
    }

    while x % 3 == 0 {
        x = x / 3;
    }

    while x % 5 == 0 {
        x = x / 5;
    }

    x == 1
}
