pub fn make_the_integer_zero(num1: i64, num2: i64) -> i64 {
    let mut k: i64 = 1;

    while k <= 60 {
        let x = num1 - k * num2;

        if x >= k {
            let mut y = x;
            let mut bits: i64 = 0;

            while y > 0 {
                bits = bits + y % 2;
                y = y / 2;
            }

            if bits <= k {
                return k;
            }
        }

        k = k + 1;
    }

    -1
}
