pub fn next_greater_element(n: i64) -> i64 {
    let mut x = n;
    let mut rev_digits: Vec<i64> = Vec::new();

    while x > 0 {
        rev_digits.push(x % 10);
        x = x / 10;
    }

    let mut len = rev_digits.len();
    let mut digits: Vec<i64> = Vec::new();
    let mut idx = len;
    while idx > 0 {
        idx -= 1;
        digits.push(rev_digits[idx]);
    }

    len = digits.len();
    if len <= 1 {
        return -1;
    }

    let mut pivot: usize = len;
    let mut j: usize = len - 1;

    while j > 0 {
        let left = j - 1;
        if digits[left] < digits[j] {
            pivot = left;
            break;
        }
        j -= 1;
    }

    if pivot == len {
        return -1;
    }

    let mut k: usize = len - 1;
    while k > pivot {
        if digits[k] > digits[pivot] {
            break;
        }
        k -= 1;
    }

    let tmp = digits[pivot];
    digits[pivot] = digits[k];
    digits[k] = tmp;

    let mut left: usize = pivot + 1;
    let mut right: usize = len - 1;
    while left < right {
        let t = digits[left];
        digits[left] = digits[right];
        digits[right] = t;
        left += 1;
        right -= 1;
    }

    let mut result: i64 = 0;
    let mut i: usize = 0;
    while i < len {
        result = result * 10 + digits[i];
        i += 1;
    }

    if result > 2147483647 {
        return -1;
    }

    result
}
