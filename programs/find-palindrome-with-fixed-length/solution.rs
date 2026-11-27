fn pow10(exp: i64) -> i64 {
    let mut result = 1;
    let mut e = exp;
    while e > 0 {
        result *= 10;
        e -= 1;
    }
    result
}

fn reverse_digits(x0: i64) -> i64 {
    let mut x = x0;
    let mut result = 0;
    while x > 0 {
        result = result * 10 + x % 10;
        x /= 10;
    }
    result
}

pub fn kth_palindrome(queries: &[i64], intLength: i64) -> Vec<i64> {
    let mut answer: Vec<i64> = Vec::new();

    let half_len = (intLength + 1) / 2;
    let smallest_half = pow10(half_len - 1);
    let count = 9 * smallest_half;

    let mut i = 0;
    while i < queries.len() {
        let q = queries[i];

        if q < 1 || q > count {
            answer.push(-1);
        } else {
            let half = smallest_half + q - 1;
            let palindrome: i64;

            if intLength % 2 == 0 {
                palindrome = half * pow10(half_len) + reverse_digits(half);
            } else {
                palindrome = half * pow10(half_len - 1) + reverse_digits(half / 10);
            }

            answer.push(palindrome);
        }

        i += 1;
    }

    answer
}
