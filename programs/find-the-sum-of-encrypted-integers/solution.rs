fn encrypt(mut x: i64) -> i64 {
    let mut max_digit: i64 = 0;
    let mut len: i64 = 0;

    while x > 0 {
        let d: i64 = x % 10;
        if d > max_digit {
            max_digit = d;
        }
        len = len + 1;
        x = x / 10;
    }

    if len == 0 {
        return 0;
    }

    let mut res: i64 = 0;
    let mut i: i64 = 0;
    while i < len {
        res = res * 10 + max_digit;
        i = i + 1;
    }

    res
}

pub fn sum_of_encrypted_int(nums: &[i64]) -> i64 {
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < nums.len() {
        total = total + encrypt(nums[i]);
        i = i + 1;
    }

    total
}
