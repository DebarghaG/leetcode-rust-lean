fn trib_helper(k: i64, a: i64, b: i64, c: i64) -> i64 {
    if k == 0 {
        a
    } else {
        trib_helper(k - 1, b, c, a + b + c)
    }
}

pub fn tribonacci(n: i64) -> i64 {
    trib_helper(n, 0, 1, 1)
}
