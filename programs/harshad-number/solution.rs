pub fn sum_of_the_digits_of_harshad_number(x: i64) -> i64 {
    let mut n: i64 = x;
    let mut sum: i64 = 0;

    while n > 0 {
        sum += n % 10;
        n /= 10;
    }

    if x % sum == 0 {
        sum
    } else {
        -1
    }
}
