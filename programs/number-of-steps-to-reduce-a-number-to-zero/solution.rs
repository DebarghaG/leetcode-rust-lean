pub fn number_of_steps(num: i64) -> i64 {
    let mut n = num;
    let mut steps: i64 = 0;
    while n > 0 {
        if n % 2 == 0 {
            n = n / 2;
        } else {
            n = n - 1;
        }
        steps = steps + 1;
    }
    steps
}
