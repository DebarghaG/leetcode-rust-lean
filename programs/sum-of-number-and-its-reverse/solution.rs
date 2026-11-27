fn reverse_number(mut n: i64) -> i64 {
    let mut rev: i64 = 0;
    while n > 0 {
        rev = rev * 10 + n % 10;
        n = n / 10;
    }
    rev
}

pub fn sum_of_number_and_reverse(num: i64) -> bool {
    let mut i: i64 = 0;
    while i <= num {
        if i + reverse_number(i) == num {
            return true;
        }
        i += 1;
    }
    false
}
