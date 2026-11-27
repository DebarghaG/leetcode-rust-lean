pub fn count_operations(num1: i64, num2: i64) -> i64 {
    let mut a = num1;
    let mut b = num2;
    let mut count = 0i64;

    while a > 0 && b > 0 {
        if a >= b {
            a = a - b;
        } else {
            b = b - a;
        }
        count = count + 1;
    }

    count
}
