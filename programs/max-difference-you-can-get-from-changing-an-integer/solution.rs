pub fn max_diff(num: i64) -> i64 {
    let digits = to_digits(num);
    let n = digits.len();

    // Find the maximum possible value.
    let mut x_max: i64 = -1;
    let mut i: usize = 0;
    while i < n {
        if x_max == -1 && digits[i] != 9 {
            x_max = digits[i];
        }
        i += 1;
    }

    let max_val: i64;
    if x_max == -1 {
        max_val = num;
    } else {
        max_val = replace_digits(&digits, x_max, 9);
    }

    // Find the minimum possible value.
    let mut x_min: i64 = -1;
    let mut y_min: i64 = 0;

    if digits[0] != 1 {
        x_min = digits[0];
        y_min = 1;
    } else {
        let mut j: usize = 1;
        while j < n {
            if x_min == -1 && digits[j] != 0 && digits[j] != 1 {
                x_min = digits[j];
                y_min = 0;
            }
            j += 1;
        }
    }

    let min_val: i64;
    if x_min == -1 {
        min_val = num;
    } else {
        min_val = replace_digits(&digits, x_min, y_min);
    }

    max_val - min_val
}

fn to_digits(mut num: i64) -> Vec<i64> {
    let mut reversed: Vec<i64> = Vec::new();

    while num > 0 {
        reversed.push(num % 10);
        num = num / 10;
    }

    let n = reversed.len();
    let mut digits: Vec<i64> = Vec::new();
    let mut i = n;

    while i > 0 {
        i -= 1;
        digits.push(reversed[i]);
    }

    digits
}

fn replace_digits(digits: &[i64], x: i64, y: i64) -> i64 {
    let mut value: i64 = 0;
    let n = digits.len();
    let mut i: usize = 0;

    while i < n {
        let mut d = digits[i];
        if d == x {
            d = y;
        }
        value = value * 10 + d;
        i += 1;
    }

    value
}
