fn number_bytes(mut x: i64) -> Vec<u8> {
    let mut digits: Vec<u8> = Vec::new();
    if x == 0 {
        digits.push(b'0');
        return digits;
    }

    let mut rev: Vec<u8> = Vec::new();
    while x > 0 {
        let d: u8 = (x % 10) as u8;
        rev.push(b'0' + d);
        x = x / 10;
    }

    let mut k: usize = rev.len();
    while k > 0 {
        k -= 1;
        digits.push(rev[k]);
    }
    digits
}

pub fn ip_to_cidr(ip: &[u8], n: i64) -> Vec<Vec<u8>> {
    let mut cur: i64 = 0;
    let mut part: i64 = 0;
    let mut i: usize = 0;

    while i < ip.len() {
        let ch: u8 = ip[i];
        if ch == b'.' {
            cur = cur * 256 + part;
            part = 0;
        } else {
            part = part * 10 + (ch - b'0') as i64;
        }
        i += 1;
    }
    cur = cur * 256 + part;

    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut remaining: i64 = n;

    while remaining > 0 {
        let mut size: i64 = 1;
        while size * 2 <= remaining {
            if cur % (size * 2) == 0 {
                size = size * 2;
            } else {
                break;
            }
        }

        let mut block: Vec<u8> = Vec::new();
        let mut x: i64 = cur;

        let o1: i64 = x / 16777216;
        x = x % 16777216;
        let o2: i64 = x / 65536;
        x = x % 65536;
        let o3: i64 = x / 256;
        x = x % 256;
        let o4: i64 = x;

        let b1 = number_bytes(o1);
        let mut j: usize = 0;
        while j < b1.len() {
            block.push(b1[j]);
            j += 1;
        }
        block.push(b'.');

        let b2 = number_bytes(o2);
        j = 0;
        while j < b2.len() {
            block.push(b2[j]);
            j += 1;
        }
        block.push(b'.');

        let b3 = number_bytes(o3);
        j = 0;
        while j < b3.len() {
            block.push(b3[j]);
            j += 1;
        }
        block.push(b'.');

        let b4 = number_bytes(o4);
        j = 0;
        while j < b4.len() {
            block.push(b4[j]);
            j += 1;
        }

        block.push(b'/');

        let mut prefix: i64 = 32;
        let mut t: i64 = size;
        while t > 1 {
            prefix -= 1;
            t = t / 2;
        }

        let bp = number_bytes(prefix);
        j = 0;
        while j < bp.len() {
            block.push(bp[j]);
            j += 1;
        }

        out.push(block);

        cur = cur + size;
        remaining = remaining - size;
    }

    out
}
