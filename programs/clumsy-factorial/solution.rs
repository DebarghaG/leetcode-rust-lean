pub fn clumsy(n: i64) -> i64 {
    let mut total: i64 = 0;
    let mut term: i64 = n;
    let mut sign: i64 = 1;
    let mut x: i64 = n - 1;
    let mut op: i64 = 0;

    while x >= 1 {
        if op == 0 {
            term = term * x;
        } else if op == 1 {
            term = term / x;
        } else if op == 2 {
            total = total + sign * term;
            sign = 1;
            term = x;
        } else {
            total = total + sign * term;
            sign = -1;
            term = x;
        }

        x = x - 1;
        op = op + 1;
        if op == 4 {
            op = 0;
        }
    }

    total + sign * term
}
