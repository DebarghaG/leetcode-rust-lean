pub fn alternate_digit_sum(n: i64) -> i64 {
    let mut temp: i64 = n;
    let mut len: usize = 0;

    while temp > 0 {
        len += 1;
        temp /= 10;
    }

    let mut divisor: i64 = 1;
    let mut j: usize = 1;
    while j < len {
        divisor *= 10;
        j += 1;
    }

    let mut sum: i64 = 0;
    let mut i: usize = 0;

    while i < len {
        let digit: i64 = (n / divisor) % 10;

        if i % 2 == 0 {
            sum += digit;
        } else {
            sum -= digit;
        }

        divisor /= 10;
        i += 1;
    }

    sum
}
