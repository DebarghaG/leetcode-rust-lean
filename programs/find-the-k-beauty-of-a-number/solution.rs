pub fn divisor_substrings(num: i64, k: i64) -> i64 {
    if num <= 0 || k <= 0 {
        return 0;
    }

    let mut digits: Vec<i64> = Vec::new();
    let mut n: i64 = num;
    while n > 0 {
        digits.push(n % 10);
        n = n / 10;
    }

    let dlen: usize = digits.len();

    let mut left: usize = 0;
    let mut right: usize = dlen;
    while left < right {
        right = right - 1;
        let tmp = digits[left];
        digits[left] = digits[right];
        digits[right] = tmp;
        left = left + 1;
    }

    let width: usize = k as usize;
    if width > dlen {
        return 0;
    }

    let last_start: usize = dlen - width;
    let mut count: i64 = 0;
    let mut start: usize = 0;

    while start <= last_start {
        let mut value: i64 = 0;
        let mut idx: usize = start;
        let end: usize = start + width;

        while idx < end {
            value = value * 10 + digits[idx];
            idx = idx + 1;
        }

        if value != 0 && num % value == 0 {
            count = count + 1;
        }

        start = start + 1;
    }

    count
}
