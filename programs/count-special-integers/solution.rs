fn digit_perm(a: i64, k: i64) -> i64 {
    if k > a {
        return 0;
    }

    let mut res: i64 = 1;
    let mut t: i64 = 0;
    while t < k {
        res = res * (a - t);
        t = t + 1;
    }
    res
}

fn number_to_digits(mut n: i64) -> Vec<i64> {
    let mut rev: Vec<i64> = Vec::new();
    while n > 0 {
        rev.push(n % 10);
        n = n / 10;
    }

    let mut digits: Vec<i64> = Vec::new();
    let mut i: usize = rev.len();
    while i > 0 {
        i = i - 1;
        let d: i64 = rev[i];
        digits.push(d);
    }
    digits
}

pub fn count_special_numbers(n: i64) -> i64 {
    if n <= 0 {
        return 0;
    }

    let digits: Vec<i64> = number_to_digits(n);
    let len_usize: usize = digits.len();
    let len_i: i64 = len_usize as i64;

    let mut ans: i64 = 0;

    // Count all special numbers with fewer digits than n.
    let mut l: i64 = 1;
    while l < len_i {
        if l == 1 {
            ans = ans + 9;
        } else {
            ans = ans + 9 * digit_perm(9, l - 1);
        }
        l = l + 1;
    }

    // Count special numbers with the same number of digits as n and <= n.
    let mut used: i64 = 0;
    let mut pos: usize = 0;
    while pos < len_usize {
        let d: i64 = digits[pos];
        let low: i64 = if pos == 0 { 1 } else { 0 };
        let pos_i: i64 = pos as i64;

        let mut c: i64 = low;
        while c < d {
            if (used & (1i64 << c)) == 0 {
                let available: i64 = 10 - (pos_i + 1);
                let rem: i64 = len_i - pos_i - 1;
                ans = ans + digit_perm(available, rem);
            }
            c = c + 1;
        }

        if (used & (1i64 << d)) != 0 {
            return ans;
        }

        used = used | (1i64 << d);
        pos = pos + 1;
    }

    // n itself is special.
    ans = ans + 1;
    ans
}
