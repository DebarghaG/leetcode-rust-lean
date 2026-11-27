pub fn plus_one(digits: &[i64]) -> Vec<i64> {
    let n = digits.len();
    let mut out: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        out.push(digits[i]);
        i += 1;
    }

    let mut j: usize = n;
    let mut carry: i64 = 1;

    while j > 0 && carry == 1 {
        let idx: usize = j - 1;
        let val: i64 = out[idx] + 1;
        if val == 10 {
            out[idx] = 0;
            carry = 1;
        } else {
            out[idx] = val;
            carry = 0;
        }
        j = idx;
    }

    if carry == 1 {
        let mut res: Vec<i64> = Vec::new();
        res.push(1);
        let mut k: usize = 0;
        while k < n {
            res.push(out[k]);
            k += 1;
        }
        return res;
    }

    out
}
