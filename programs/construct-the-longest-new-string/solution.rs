pub fn longest_string(x: i64, y: i64, z: i64) -> i64 {
    let mut m = x;
    if y < m {
        m = y;
    }

    let mut extra = 1;
    if x == y {
        extra = 0;
    }

    2 * (z + 2 * m + extra)
}
