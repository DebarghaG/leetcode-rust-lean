pub fn subdomain_visits(cpdomains: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let mut keys: Vec<Vec<u8>> = Vec::new();
    let mut vals: Vec<i64> = Vec::new();

    let mut idx = 0;
    while idx < cpdomains.len() {
        let s = &cpdomains[idx];

        let mut p = 0;
        let mut num: i64 = 0;
        while p < s.len() && s[p] != b' ' {
            num = num * 10 + byte_digit(s[p]);
            p = p + 1;
        }

        let start = p + 1;
        process(&mut keys, &mut vals, s, start, num);

        let mut q = start;
        while q < s.len() {
            if s[q] == b'.' {
                process(&mut keys, &mut vals, s, q + 1, num);
            }
            q = q + 1;
        }

        idx = idx + 1;
    }

    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut i = 0;
    while i < keys.len() {
        add_result(&mut result, &keys[i], vals[i]);
        i = i + 1;
    }
    result
}

fn process(keys: &mut Vec<Vec<u8>>, vals: &mut Vec<i64>, s: &Vec<u8>, start: usize, count: i64) {
    let key_len = s.len() - start;

    let mut i = 0;
    while i < keys.len() {
        let row = &keys[i];
        let mut same = row.len() == key_len;

        if same {
            let mut j = 0;
            while j < key_len {
                if row[j] != s[start + j] {
                    same = false;
                }
                j = j + 1;
            }
        }

        if same {
            let mut nv: Vec<i64> = Vec::new();
            let mut t = 0;
            while t < vals.len() {
                if t == i {
                    nv.push(vals[t] + count);
                } else {
                    nv.push(vals[t]);
                }
                t = t + 1;
            }
            *vals = nv;
            return;
        }

        i = i + 1;
    }

    let mut key: Vec<u8> = Vec::new();
    let mut j = 0;
    while j < key_len {
        key.push(s[start + j]);
        j = j + 1;
    }

    keys.push(key);
    vals.push(count);
}

fn add_result(result: &mut Vec<Vec<u8>>, domain: &Vec<u8>, count: i64) {
    let mut row: Vec<u8> = Vec::new();
    push_count(&mut row, count);
    row.push(b' ');

    let mut i = 0;
    while i < domain.len() {
        row.push(domain[i]);
        i = i + 1;
    }

    result.push(row);
}

fn push_count(out: &mut Vec<u8>, x: i64) {
    if x == 0 {
        out.push(b'0');
        return;
    }

    let mut tmp: Vec<u8> = Vec::new();
    let mut v = x;

    while v > 0 {
        let d = v % 10;
        tmp.push(digit_byte(d));
        v = v / 10;
    }

    let mut i = tmp.len();
    while i > 0 {
        i = i - 1;
        out.push(tmp[i]);
    }
}

fn byte_digit(b: u8) -> i64 {
    if b == b'0' {
        return 0;
    }
    if b == b'1' {
        return 1;
    }
    if b == b'2' {
        return 2;
    }
    if b == b'3' {
        return 3;
    }
    if b == b'4' {
        return 4;
    }
    if b == b'5' {
        return 5;
    }
    if b == b'6' {
        return 6;
    }
    if b == b'7' {
        return 7;
    }
    if b == b'8' {
        return 8;
    }
    if b == b'9' {
        return 9;
    }
    0
}

fn digit_byte(d: i64) -> u8 {
    if d == 0 {
        return b'0';
    }
    if d == 1 {
        return b'1';
    }
    if d == 2 {
        return b'2';
    }
    if d == 3 {
        return b'3';
    }
    if d == 4 {
        return b'4';
    }
    if d == 5 {
        return b'5';
    }
    if d == 6 {
        return b'6';
    }
    if d == 7 {
        return b'7';
    }
    if d == 8 {
        return b'8';
    }
    b'9'
}
