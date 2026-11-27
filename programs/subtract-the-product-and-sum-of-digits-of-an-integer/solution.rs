pub fn subtract_product_and_sum(n: i64) -> i64 {
    let mut m = n;
    let mut product: i64 = 1;
    let mut sum: i64 = 0;

    while m > 0 {
        let digit = m % 10;
        product = product * digit;
        sum = sum + digit;
        m = m / 10;
    }

    product - sum
}
