pub fn fill_cups(amount: &[i64]) -> i64 {
    let a = amount[0];
    let b = amount[1];
    let c = amount[2];

    let total = a + b + c;

    let mut max_amount = a;
    if b > max_amount {
        max_amount = b;
    }
    if c > max_amount {
        max_amount = c;
    }

    let half_ceiling = (total + 1) / 2;

    if max_amount > half_ceiling {
        max_amount
    } else {
        half_ceiling
    }
}
