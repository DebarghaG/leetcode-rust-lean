pub fn concatenated_binary(n: i64) -> i64 {
    let modulus: i64 = 1000000007;
    let mut ans: i64 = 0;
    let mut i: i64 = 1;
    let mut next_power: i64 = 2;
    let mut base: i64 = 2;

    while i <= n {
        if i >= next_power {
            next_power *= 2;
            base *= 2;
        }

        ans = (ans * base + i) % modulus;
        i += 1;
    }

    ans
}
