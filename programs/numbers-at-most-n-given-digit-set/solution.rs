pub fn at_most_n_given_digit_set(digits: &[Vec<u8>], n: i64) -> i64 {
    let m = digits.len();

    let mut ds: Vec<i64> = Vec::new();
    let mut md: i64 = 0;
    let mut i: usize = 0;

    while i < m {
        let b = digits[i][0];
        let mut v: i64 = 0;

        if b == b'1' {
            v = 1;
        } else if b == b'2' {
            v = 2;
        } else if b == b'3' {
            v = 3;
        } else if b == b'4' {
            v = 4;
        } else if b == b'5' {
            v = 5;
        } else if b == b'6' {
            v = 6;
        } else if b == b'7' {
            v = 7;
        } else if b == b'8' {
            v = 8;
        } else if b == b'9' {
            v = 9;
        }

        ds.push(v);
        md = md + 1;
        i = i + 1;
    }

    let mut rev: Vec<i64> = Vec::new();
    let mut x = n;

    while x > 0 {
        rev.push(x % 10);
        x = x / 10;
    }

    let l = rev.len();

    let mut ans: i64 = 0;
    let mut power: i64 = 1;
    let mut k: usize = 1;

    while k < l {
        power = power * md;
        ans = ans + power;
        k = k + 1;
    }

    let mut p: i64 = 1;
    let mut e: usize = 0;

    while e + 1 < l {
        p = p * md;
        e = e + 1;
    }

    let mut pos: usize = 0;

    while pos < l {
        let d = rev[l - 1 - pos];
        let remaining = l - 1 - pos;

        let mut c: i64 = 0;
        let mut j: usize = 0;

        while j < m {
            if ds[j] < d {
                c = c + 1;
            }
            j = j + 1;
        }

        ans = ans + c * p;

        let mut contains: bool = false;
        j = 0;

        while j < m {
            if ds[j] == d {
                contains = true;
            }
            j = j + 1;
        }

        if !contains {
            return ans;
        }

        if remaining > 0 {
            p = p / md;
        }

        pos = pos + 1;
    }

    ans + 1
}
