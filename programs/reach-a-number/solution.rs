pub fn reach_number(target: i64) -> i64 {
    let mut n = target;
    if n < 0 {
        n = -n;
    }

    let mut k: i64 = 0;
    let mut sum: i64 = 0;

    while sum < n || (sum - n) % 2 != 0 {
        k += 1;
        sum += k;
    }

    k
}
