pub fn count_prime_set_bits(left: i64, right: i64) -> i64 {
    let mut ans: i64 = 0;
    let mut n: i64 = left;

    while n <= right {
        let mut x: i64 = n;
        let mut bits: i64 = 0;

        while x > 0 {
            if x % 2 == 1 {
                bits += 1;
            }
            x = x / 2;
        }

        if bits == 2
            || bits == 3
            || bits == 5
            || bits == 7
            || bits == 11
            || bits == 13
            || bits == 17
            || bits == 19
        {
            ans += 1;
        }

        n += 1;
    }

    ans
}
