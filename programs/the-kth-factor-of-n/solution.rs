pub fn kth_factor(n: i64, k: i64) -> i64 {
    let mut count: i64 = 0;
    let mut i: i64 = 1;

    while i <= n {
        if n % i == 0 {
            count += 1;
            if count == k {
                return i;
            }
        }
        i += 1;
    }

    -1
}
