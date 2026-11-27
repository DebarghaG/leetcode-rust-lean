const MOD: i64 = 1000000007;

fn add_mod(a: i64, b: i64) -> i64 {
    let s = a + b;
    if s >= MOD {
        s - MOD
    } else {
        s
    }
}

fn sub_mod(a: i64, b: i64) -> i64 {
    if a >= b {
        a - b
    } else {
        a + MOD - b
    }
}

fn digit_val(b: u8) -> usize {
    if b == b'0' {
        0
    } else if b == b'1' {
        1
    } else if b == b'2' {
        2
    } else if b == b'3' {
        3
    } else if b == b'4' {
        4
    } else if b == b'5' {
        5
    } else if b == b'6' {
        6
    } else if b == b'7' {
        7
    } else if b == b'8' {
        8
    } else {
        9
    }
}

fn is_stepping(s: &[u8]) -> bool {
    let n = s.len();
    if n == 0 {
        return false;
    }
    if s[0] == b'0' {
        return false;
    }

    let mut i: usize = 1;
    while i < n {
        let a = digit_val(s[i - 1]);
        let b = digit_val(s[i]);
        let diff = if a > b { a - b } else { b - a };
        if diff != 1 {
            return false;
        }
        i += 1;
    }
    true
}

fn build_ways(n: usize) -> Vec<i64> {
    let mut table: Vec<i64> = Vec::new();

    let mut j: usize = 0;
    while j < 10 {
        table.push(1);
        j += 1;
    }

    let mut rem: usize = 1;
    while rem < n {
        let prev_base: usize = (rem - 1) * 10;
        let mut last: usize = 0;
        while last < 10 {
            let mut s: i64 = 0;
            if last > 0 {
                s = add_mod(s, table[prev_base + (last - 1)]);
            }
            if last < 9 {
                s = add_mod(s, table[prev_base + (last + 1)]);
            }
            table.push(s);
            last += 1;
        }
        rem += 1;
    }

    table
}

fn count_le(x: &[u8]) -> i64 {
    let n = x.len();
    if n == 0 {
        return 0;
    }

    let table = build_ways(n);
    let mut total: i64 = 0;

    let mut len: usize = 1;
    while len < n {
        let base: usize = (len - 1) * 10;
        let mut first: usize = 1;
        while first <= 9 {
            total = add_mod(total, table[base + first]);
            first += 1;
        }
        len += 1;
    }

    let mut pos: usize = 0;
    let mut prev: usize = 0;
    let mut tight: bool = true;

    while pos < n && tight {
        let xd = digit_val(x[pos]);
        let rem2: usize = n - pos - 1;
        let base_rem: usize = rem2 * 10;

        let mut d: usize = 0;
        while d < xd {
            let mut ok: bool = false;
            if pos == 0 {
                if d >= 1 {
                    ok = true;
                }
            } else {
                if d + 1 == prev {
                    ok = true;
                }
                if prev + 1 == d {
                    ok = true;
                }
            }

            if ok {
                total = add_mod(total, table[base_rem + d]);
            }
            d += 1;
        }

        let mut ok_xd: bool = false;
        if pos == 0 {
            if xd >= 1 {
                ok_xd = true;
            }
        } else {
            if xd + 1 == prev {
                ok_xd = true;
            }
            if prev + 1 == xd {
                ok_xd = true;
            }
        }

        if ok_xd {
            prev = xd;
            pos += 1;
        } else {
            tight = false;
        }
    }

    if tight {
        total = add_mod(total, 1);
    }

    total
}

pub fn count_stepping_numbers(low: &[u8], high: &[u8]) -> i64 {
    let hi = count_le(high);
    let lo = count_le(low);

    let mut ans = sub_mod(hi, lo);
    if is_stepping(low) {
        ans = add_mod(ans, 1);
    }

    ans
}
