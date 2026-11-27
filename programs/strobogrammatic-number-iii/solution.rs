fn parse_num(s: &[u8]) -> i64 {
    let mut v: i64 = 0;
    let mut i: usize = 0;
    while i < s.len() {
        let d: i64 = (s[i] - b'0') as i64;
        v = v * 10 + d;
        i += 1;
    }
    v
}

fn right_of(d: i64) -> i64 {
    if d == 0 {
        0
    } else if d == 1 {
        1
    } else if d == 6 {
        9
    } else if d == 8 {
        8
    } else {
        6
    }
}

fn pow10_i64(e: usize) -> i64 {
    let mut p: i64 = 1;
    let mut k: usize = 0;
    while k < e {
        p = p * 10;
        k += 1;
    }
    p
}

fn count_exact_len(len: usize, low: i64, high: i64) -> i64 {
    if len == 1 {
        let mut cnt: i64 = 0;
        if low <= 0 && 0 <= high {
            cnt += 1;
        }
        if low <= 1 && 1 <= high {
            cnt += 1;
        }
        if low <= 8 && 8 <= high {
            cnt += 1;
        }
        return cnt;
    }

    let mut vals: Vec<i64> = Vec::new();
    let mut cur_len: usize;

    if len % 2 == 1 {
        vals.push(0);
        vals.push(1);
        vals.push(8);
        cur_len = 1;
    } else {
        vals.push(0);
        cur_len = 0;
    }

    while cur_len + 2 <= len {
        let outermost: bool = cur_len + 2 == len;

        let mut lefts: Vec<i64> = Vec::new();
        if outermost {
            lefts.push(1);
            lefts.push(6);
            lefts.push(8);
            lefts.push(9);
        } else {
            lefts.push(0);
            lefts.push(1);
            lefts.push(6);
            lefts.push(8);
            lefts.push(9);
        }

        let place: i64 = pow10_i64(cur_len + 1);
        let mut next: Vec<i64> = Vec::new();

        let mut vi: usize = 0;
        while vi < vals.len() {
            let inner: i64 = vals[vi];

            let mut li: usize = 0;
            while li < lefts.len() {
                let left: i64 = lefts[li];
                let right: i64 = right_of(left);
                let value: i64 = left * place + inner * 10 + right;
                next.push(value);
                li += 1;
            }

            vi += 1;
        }

        vals = next;
        cur_len += 2;
    }

    let mut cnt: i64 = 0;
    let mut idx: usize = 0;
    while idx < vals.len() {
        let x: i64 = vals[idx];
        if low <= x && x <= high {
            cnt += 1;
        }
        idx += 1;
    }

    cnt
}

pub fn strobogrammatic_in_range(low: &[u8], high: &[u8]) -> i64 {
    let lo: i64 = parse_num(low);
    let hi: i64 = parse_num(high);
    let max_len: usize = high.len();

    let mut ans: i64 = 0;
    let mut len: usize = 1;
    while len <= max_len {
        ans += count_exact_len(len, lo, hi);
        len += 1;
    }

    ans
}
