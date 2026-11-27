pub fn min_changes(n: i64, k: i64) -> i64 {
    let mut a = n;
    let mut b = k;
    let mut count: i64 = 0;

    while a > 0 || b > 0 {
        let abit = a % 2;
        let bbit = b % 2;

        if bbit == 1 && abit == 0 {
            return -1;
        }

        if abit == 1 && bbit == 0 {
            count += 1;
        }

        a = a / 2;
        b = b / 2;
    }

    count
}
