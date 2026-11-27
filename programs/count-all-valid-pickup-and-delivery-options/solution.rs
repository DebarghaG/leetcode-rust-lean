pub fn count_orders(n: i64) -> i64 {
    let modulo: i64 = 1000000007;
    let mut ans: i64 = 1;
    let mut i: i64 = 1;

    while i <= n {
        ans = (ans * i) % modulo;
        ans = (ans * (2 * i - 1)) % modulo;
        i += 1;
    }

    ans
}
