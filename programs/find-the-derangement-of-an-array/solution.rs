pub fn find_derangement(n: i64) -> i64 {
    let modv: i64 = 1000000007;

    if n <= 0 {
        return 1;
    }
    if n == 1 {
        return 0;
    }
    if n == 2 {
        return 1;
    }

    let mut prev2: i64 = 0; // D(1)
    let mut prev1: i64 = 1; // D(2)

    let mut i: i64 = 3;
    while i <= n {
        let sum: i64 = (prev1 + prev2) % modv;
        let cur: i64 = ((i - 1) * sum) % modv;

        prev2 = prev1;
        prev1 = cur;
        i += 1;
    }

    prev1
}
