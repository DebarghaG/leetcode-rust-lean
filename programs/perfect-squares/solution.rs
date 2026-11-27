pub fn num_squares(n: i64) -> i64 {
    if n <= 0 {
        return 0;
    }

    // Compute floor(sqrt(n)).
    let mut b: i64 = 0;
    while (b + 1) * (b + 1) <= n {
        b += 1;
    }

    // If n is itself a perfect square, the answer is 1.
    if b * b == n {
        return 1;
    }

    // Legendre's three-square theorem:
    // n = 4^a * (8b + 7) iff n needs exactly four squares.
    let mut m: i64 = n;
    while m % 4 == 0 {
        m = m / 4;
    }
    if m % 8 == 7 {
        return 4;
    }

    // Check whether n is a sum of two squares using two pointers.
    let mut a: i64 = 0;
    while a <= b {
        let s = a * a + b * b;
        if s == n {
            return 2;
        }
        if s < n {
            a += 1;
        } else {
            b -= 1;
        }
    }

    // Otherwise, by Lagrange's four-square theorem and the checks above,
    // the answer is exactly 3.
    3
}
