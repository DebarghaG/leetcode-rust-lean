pub fn smallest_number(n: i64, t: i64) -> i64 {
    let mut x = n;
    let limit = n + 9;

    while x <= limit {
        let mut m = x;
        let mut product = 1i64;

        while m > 0 {
            let digit = m % 10;
            product = product * digit;
            m = m / 10;
        }

        if product % t == 0 {
            return x;
        }

        x += 1;
    }

    n + 9
}
