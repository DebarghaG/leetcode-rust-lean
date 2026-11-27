pub fn count_digits(num: i64) -> i64 {
    let mut count: i64 = 0;
    let mut temp: i64 = num;

    while temp > 0 {
        let digit: i64 = temp % 10;
        if digit != 0 && num % digit == 0 {
            count += 1;
        }
        temp = temp / 10;
    }

    count
}
