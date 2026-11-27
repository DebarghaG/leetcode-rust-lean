pub fn check_perfect_number(num: i64) -> bool {
    if num <= 1 {
        return false;
    }

    let mut sum: i64 = 1;
    let mut i: i64 = 2;

    while i * i <= num {
        if num % i == 0 {
            sum += i;
            let other = num / i;
            if other != i {
                sum += other;
            }
        }
        i += 1;
    }

    sum == num
}
