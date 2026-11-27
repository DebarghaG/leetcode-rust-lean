fn parse_num(num: &[u8], start: usize, len: usize) -> i64 {
    if len == 0 {
        return -1;
    }
    if num[start] == b'0' && len > 1 {
        return -1;
    }

    let mut val: i64 = 0;
    let mut i: usize = 0;
    let mut ok: bool = true;
    while i < len && ok {
        let d: i64 = (num[start + i] - b'0') as i64;
        if val > 214748364 {
            ok = false;
        } else {
            val = val * 10 + d;
            if val >= 2147483648 {
                ok = false;
            } else {
                i = i + 1;
            }
        }
    }

    if ok {
        val
    } else {
        -1
    }
}

fn try_sequence(num: &[u8], start: usize, first: i64, second: i64) -> Vec<i64> {
    let n: usize = num.len();
    let mut seq: Vec<i64> = Vec::new();
    seq.push(first);
    seq.push(second);

    let mut a: i64 = first;
    let mut b: i64 = second;
    let mut pos: usize = start;
    let mut valid: bool = true;

    while pos < n && valid {
        let c: i64 = a + b;
        if c >= 2147483648 {
            valid = false;
        } else {
            let mut len: usize = 1;
            let mut place: i64 = 1;
            let mut temp: i64 = c;
            while temp >= 10 {
                temp = temp / 10;
                len = len + 1;
                place = place * 10;
            }

            if pos + len > n {
                valid = false;
            } else {
                let mut k: usize = 0;
                let mut divisor: i64 = place;
                let mut match_ok: bool = true;
                while k < len && match_ok {
                    let digit: i64 = (c / divisor) % 10;
                    let actual: i64 = (num[pos + k] - b'0') as i64;
                    if digit == actual {
                        divisor = divisor / 10;
                        k = k + 1;
                    } else {
                        match_ok = false;
                    }
                }

                if match_ok {
                    pos = pos + len;
                    seq.push(c);
                    a = b;
                    b = c;
                } else {
                    valid = false;
                }
            }
        }
    }

    if valid && seq.len() >= 3 {
        seq
    } else {
        Vec::new()
    }
}

pub fn split_into_fibonacci(num: &[u8]) -> Vec<i64> {
    let n: usize = num.len();
    if n < 3 {
        return Vec::new();
    }

    let mut result: Vec<i64> = Vec::new();
    let mut found: bool = false;

    let mut l1: usize = 1;
    while l1 + 2 <= n && !found {
        let mut skip1: bool = false;
        if l1 > 1 && num[0] == b'0' {
            skip1 = true;
        }

        if !skip1 {
            let a: i64 = parse_num(num, 0, l1);
            if a >= 0 {
                let mut l2: usize = 1;
                let mut stop2: bool = false;
                while l1 + l2 + 1 <= n && !found && !stop2 {
                    let mut skip2: bool = false;
                    if l2 > 1 && num[l1] == b'0' {
                        skip2 = true;
                        stop2 = true;
                    }

                    if !skip2 {
                        let b: i64 = parse_num(num, l1, l2);
                        if b >= 0 {
                            let seq: Vec<i64> = try_sequence(num, l1 + l2, a, b);
                            if seq.len() > 0 {
                                result = seq;
                                found = true;
                            }
                        }
                    }

                    l2 = l2 + 1;
                }
            }
        }

        l1 = l1 + 1;
    }

    result
}
