pub fn split_num(num: i64) -> i64 {
    let mut n: i64 = num;
    let mut digits: Vec<i64> = Vec::new();

    while n > 0 {
        let d: i64 = n % 10;
        digits.push(d);
        n = n / 10;
    }

    let len = digits.len();

    // Manual insertion-style sort of the digits in ascending order.
    let mut i: usize = 0;
    while i < len {
        let mut j: usize = i + 1;
        while j < len {
            if digits[j] < digits[i] {
                let tmp: i64 = digits[i];
                digits[i] = digits[j];
                digits[j] = tmp;
            }
            j += 1;
        }
        i += 1;
    }

    let mut num1: i64 = 0;
    let mut num2: i64 = 0;
    let mut k: usize = 0;

    while k < len {
        if k % 2 == 0 {
            num1 = num1 * 10 + digits[k];
        } else {
            num2 = num2 * 10 + digits[k];
        }
        k += 1;
    }

    num1 + num2
}
