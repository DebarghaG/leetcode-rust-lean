fn has_unique_digits(n: i64) -> bool {
    let mut digits: Vec<i64> = Vec::new();
    let mut x = n;

    while x > 0 {
        digits.push(x % 10);
        x = x / 10;
    }

    let len = digits.len();
    let mut unique = true;
    let mut i = 0usize;

    while i < len && unique {
        let mut j = i + 1;
        while j < len {
            if digits[i] == digits[j] {
                unique = false;
            }
            j += 1;
        }
        i += 1;
    }

    unique
}

pub fn number_count(a: i64, b: i64) -> i64 {
    let mut count = 0i64;
    let mut cur = a;

    while cur <= b {
        if has_unique_digits(cur) {
            count += 1;
        }
        cur += 1;
    }

    count
}
