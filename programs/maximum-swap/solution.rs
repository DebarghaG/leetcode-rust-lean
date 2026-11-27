pub fn maximum_swap(num: i64) -> i64 {
    if num < 10 {
        return num;
    }

    let mut digits: Vec<i64> = Vec::new();
    let mut x: i64 = num;

    while x > 0 {
        digits.push(x % 10);
        x = x / 10;
    }

    let n: usize = digits.len();

    let mut i: usize = 0;
    while i < n / 2 {
        let tmp: i64 = digits[i];
        digits[i] = digits[n - 1 - i];
        digits[n - 1 - i] = tmp;
        i += 1;
    }

    let mut swap_i: usize = n;
    let mut swap_j: usize = n;

    i = 0;
    while i < n {
        if swap_i == n {
            let mut max_digit: i64 = digits[i];
            let mut best_j: usize = i;
            let mut j: usize = i + 1;

            while j < n {
                if digits[j] >= max_digit {
                    max_digit = digits[j];
                    best_j = j;
                }
                j += 1;
            }

            if max_digit > digits[i] {
                swap_i = i;
                swap_j = best_j;
            }
        }
        i += 1;
    }

    if swap_i < n {
        let tmp: i64 = digits[swap_i];
        digits[swap_i] = digits[swap_j];
        digits[swap_j] = tmp;
    }

    let mut result: i64 = 0;
    let mut k: usize = 0;
    while k < n {
        result = result * 10 + digits[k];
        k += 1;
    }

    result
}
