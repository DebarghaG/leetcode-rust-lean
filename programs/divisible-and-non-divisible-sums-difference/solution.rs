pub fn difference_of_sums(n: i64, m: i64) -> i64 {
    let mut ans: i64 = 0;
    let mut i: i64 = 1;

    while i <= n {
        if i % m == 0 {
            ans -= i;
        } else {
            ans += i;
        }
        i += 1;
    }

    ans
}
