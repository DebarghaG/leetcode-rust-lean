pub fn largest_integer(num: i64) -> i64 {
    let mut digits: Vec<i64> = Vec::new();
    let mut n = num;

    if n == 0 {
        digits.push(0);
    } else {
        while n > 0 {
            let d = n % 10;
            digits.push(d);
            n = n / 10;
        }
    }

    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 10 {
        counts.push(0);
        i += 1;
    }

    let mut idx: usize = 0;
    while idx < digits.len() {
        let d = digits[idx] as usize;
        counts[d] = counts[d] + 1;
        idx += 1;
    }

    let mut result: i64 = 0;
    let mut pos: usize = digits.len();

    while pos > 0 {
        pos -= 1;
        let original_digit = digits[pos];
        let parity = original_digit % 2;
        let mut chosen: i64 = -1;
        let mut x: i64 = 9;

        while x >= 0 {
            let xi = x as usize;
            if counts[xi] > 0 && x % 2 == parity {
                chosen = x;
                break;
            }
            x -= 1;
        }

        if chosen >= 0 {
            let ci = chosen as usize;
            counts[ci] = counts[ci] - 1;
            result = result * 10 + chosen;
        }
    }

    result
}
