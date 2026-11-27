pub fn maximum_value(strs: &[Vec<u8>]) -> i64 {
    let mut best: i64 = 0;
    let mut i: usize = 0;

    while i < strs.len() {
        let s = &strs[i];
        let mut all_digits: bool = true;
        let mut j: usize = 0;

        while j < s.len() {
            let c = s[j];
            if c < b'0' || c > b'9' {
                all_digits = false;
                break;
            }
            j += 1;
        }

        let value: i64;
        if all_digits {
            let mut num: i64 = 0;
            let mut k: usize = 0;
            while k < s.len() {
                num = num * 10 + ((s[k] - b'0') as i64);
                k += 1;
            }
            value = num;
        } else {
            value = s.len() as i64;
        }

        if value > best {
            best = value;
        }

        i += 1;
    }

    best
}
