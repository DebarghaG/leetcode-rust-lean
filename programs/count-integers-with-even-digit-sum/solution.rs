pub fn count_even(num: i64) -> i64 {
    let mut count: i64 = 0;
    let mut value: i64 = 1;

    while value <= num {
        let mut x: i64 = value;
        let mut digit_sum: i64 = 0;

        while x > 0 {
            digit_sum += x % 10;
            x /= 10;
        }

        if digit_sum % 2 == 0 {
            count += 1;
        }

        value += 1;
    }

    count
}
