fn is_no_zero(mut x: i64) -> bool {
    while x > 0 {
        let digit = x % 10;
        if digit == 0 {
            return false;
        }
        x = x / 10;
    }
    true
}

pub fn get_no_zero_integers(n: i64) -> Vec<i64> {
    let mut a: i64 = 1;

    while a < n {
        let b = n - a;
        if is_no_zero(a) && is_no_zero(b) {
            let mut result: Vec<i64> = Vec::new();
            result.push(a);
            result.push(b);
            return result;
        }
        a = a + 1;
    }

    let mut result: Vec<i64> = Vec::new();
    result.push(1);
    result.push(n - 1);
    result
}
