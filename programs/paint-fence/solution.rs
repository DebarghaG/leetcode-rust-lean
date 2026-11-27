pub fn num_ways(n: i64, k: i64) -> i64 {
    if n <= 0 {
        return 0;
    }
    if n == 1 {
        return k;
    }
    if n == 2 {
        return k * k;
    }

    let mut prev2: i64 = k;
    let mut prev1: i64 = k * k;
    let mut i: i64 = 3;

    while i <= n {
        let cur: i64 = (k - 1) * (prev1 + prev2);
        prev2 = prev1;
        prev1 = cur;
        i += 1;
    }

    prev1
}
