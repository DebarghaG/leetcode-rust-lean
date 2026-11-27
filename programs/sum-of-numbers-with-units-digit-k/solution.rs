pub fn minimum_numbers(num: i64, k: i64) -> i64 {
    if num == 0 {
        return 0;
    }

    if k == 0 {
        if num < 10 || num % 10 != 0 {
            return -1;
        }
        return 1;
    }

    let mut n: i64 = 1;
    while n <= 10 {
        if num >= n * k && (num - n * k) % 10 == 0 {
            return n;
        }
        n += 1;
    }

    -1
}
