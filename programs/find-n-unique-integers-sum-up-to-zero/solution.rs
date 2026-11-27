pub fn sum_zero(n: i64) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();
    let pairs: i64 = n / 2;
    let mut i: i64 = 1;

    while i <= pairs {
        result.push(i);
        result.push(-i);
        i += 1;
    }

    if n % 2 != 0 {
        result.push(0);
    }

    result
}
