pub fn minimum_one_bit_operations(n: i64) -> i64 {
    let mut x = n;
    let mut ans: i64 = 0;

    while x > 0 {
        ans = ans ^ x;
        x = x >> 1;
    }

    ans
}
