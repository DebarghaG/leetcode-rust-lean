pub fn add_negabinary(arr1: &[i64], arr2: &[i64]) -> Vec<i64> {
    let n1 = arr1.len();
    let n2 = arr2.len();

    let mut n = n1;
    if n2 > n {
        n = n2;
    }

    let mut rev: Vec<i64> = Vec::new();
    let mut carry: i64 = 0;

    let mut k: usize = 0;
    while k < n {
        let mut a: i64 = 0;
        if k < n1 {
            a = arr1[n1 - 1 - k];
        }

        let mut b: i64 = 0;
        if k < n2 {
            b = arr2[n2 - 1 - k];
        }

        let s = a + b + carry;
        let mut digit: i64 = 0;

        if s == -1 {
            digit = 1;
            carry = 1;
        } else if s == 0 {
            digit = 0;
            carry = 0;
        } else if s == 1 {
            digit = 1;
            carry = 0;
        } else if s == 2 {
            digit = 0;
            carry = -1;
        } else {
            digit = 1;
            carry = -1;
        }

        rev.push(digit);
        k = k + 1;
    }

    while carry != 0 {
        if carry == -1 {
            rev.push(1);
            carry = 1;
        } else {
            rev.push(1);
            carry = 0;
        }
    }

    let m = rev.len();
    let mut start: usize = m;

    let mut j = m;
    while j > 0 {
        j = j - 1;
        if rev[j] != 0 {
            start = j;
            break;
        }
    }

    let mut out: Vec<i64> = Vec::new();

    if start == m {
        out.push(0);
        return out;
    }

    let mut i = start + 1;
    while i > 0 {
        i = i - 1;
        out.push(rev[i]);
    }

    out
}
