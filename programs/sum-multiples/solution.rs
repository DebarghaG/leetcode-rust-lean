pub fn sum_of_multiples(n: i64) -> i64 {
    let mut sum: i64 = 0;
    let mut i: i64 = 1;

    while i <= n {
        if i % 3 == 0 || i % 5 == 0 || i % 7 == 0 {
            sum += i;
        }
        i += 1;
    }

    sum
}
