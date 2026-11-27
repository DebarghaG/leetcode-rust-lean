pub fn monotone_increasing_digits(n: i64) -> i64 {
    let mut digits: Vec<i64> = Vec::new();
    let mut x: i64 = n;

    if x == 0 {
        digits.push(0);
    } else {
        while x > 0 {
            digits.push(x % 10);
            x = x / 10;
        }
    }

    let len: usize = digits.len();

    // Reverse the digits so they are stored from most significant to least significant.
    let mut left: usize = 0;
    let mut right: usize = len - 1;
    while left < right {
        let tmp: i64 = digits[left];
        digits[left] = digits[right];
        digits[right] = tmp;
        left += 1;
        right -= 1;
    }

    // Scan from right to left. Whenever a decrease is found, lower the left digit
    // and make every following digit 9.
    let mut i: usize = len - 1;
    while i > 0 {
        if digits[i - 1] > digits[i] {
            digits[i - 1] = digits[i - 1] - 1;

            let mut j: usize = i;
            while j < len {
                digits[j] = 9;
                j += 1;
            }
        }
        i -= 1;
    }

    let mut ans: i64 = 0;
    let mut k: usize = 0;
    while k < len {
        ans = ans * 10 + digits[k];
        k += 1;
    }

    ans
}
