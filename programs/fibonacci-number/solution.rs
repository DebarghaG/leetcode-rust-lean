pub fn fib(n: i64) -> i64 {
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 1;
    }

    let mut a: i64 = 0;
    let mut b: i64 = 1;
    let mut i: i64 = 2;

    while i <= n {
        let c: i64 = a + b;
        a = b;
        b = c;
        i += 1;
    }

    b
}
