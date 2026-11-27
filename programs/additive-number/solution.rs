pub fn is_additive_number(num: &[u8]) -> bool {
    let n = num.len();
    if n < 3 {
        return false;
    }

    let mut result: bool = false;
    let mut stop: bool = false;
    let mut first_end: usize = 1;

    while first_end <= n - 2 && !stop && !result {
        if first_end > 1 && num[0] == b'0' {
            stop = true;
        } else {
            let mut second_end: usize = first_end + 1;
            while second_end < n && !result {
                let mut second_ok: bool = true;
                if second_end - first_end > 1 && num[first_end] == b'0' {
                    second_ok = false;
                }

                if second_ok {
                    if validate_sequence(num, 0, first_end, first_end, second_end) {
                        result = true;
                    }
                }

                second_end += 1;
            }
            first_end += 1;
        }
    }

    result
}

fn validate_sequence(
    num: &[u8],
    mut a_start: usize,
    mut a_end: usize,
    mut b_start: usize,
    mut b_end: usize,
) -> bool {
    let n = num.len();
    let mut count: i64 = 2;
    let mut next_start: usize = b_end;
    let mut ok: bool = true;

    while next_start < n && ok {
        let alen = a_end - a_start;
        let blen = b_end - b_start;
        let maxlen = if alen > blen { alen } else { blen };

        let mut chosen_end: usize = 0;
        let mut found: bool = false;

        let c_len1 = maxlen;
        if next_start + c_len1 <= n {
            let c_end1 = next_start + c_len1;
            let mut valid_c = true;
            if c_len1 > 1 && num[next_start] == b'0' {
                valid_c = false;
            }

            if valid_c {
                if add_equals_at(num, a_start, a_end, b_start, b_end, next_start, c_end1) {
                    chosen_end = c_end1;
                    found = true;
                }
            }
        }

        if !found {
            let c_len2 = maxlen + 1;
            if next_start + c_len2 <= n {
                let c_end2 = next_start + c_len2;
                let mut valid_c = true;
                if c_len2 > 1 && num[next_start] == b'0' {
                    valid_c = false;
                }

                if valid_c {
                    if add_equals_at(num, a_start, a_end, b_start, b_end, next_start, c_end2) {
                        chosen_end = c_end2;
                        found = true;
                    }
                }
            }
        }

        if !found {
            ok = false;
        } else {
            a_start = b_start;
            a_end = b_end;
            b_start = next_start;
            b_end = chosen_end;
            next_start = chosen_end;
            count += 1;
        }
    }

    ok && count >= 3
}

fn add_equals_at(
    num: &[u8],
    a_start: usize,
    a_end: usize,
    b_start: usize,
    b_end: usize,
    c_start: usize,
    c_end: usize,
) -> bool {
    let alen = a_end - a_start;
    let blen = b_end - b_start;
    let clen = c_end - c_start;
    let maxlen = if alen > blen { alen } else { blen };

    if clen < maxlen || clen > maxlen + 1 {
        return false;
    }

    let mut ia = a_end;
    let mut ib = b_end;
    let mut ic = c_end;
    let mut carry: i64 = 0;
    let mut ok: bool = true;

    while ic > c_start && ok {
        ic -= 1;
        let cd = (num[ic] as i64) - 48;

        let mut sum: i64 = carry;

        if ia > a_start {
            ia -= 1;
            sum += (num[ia] as i64) - 48;
        }

        if ib > b_start {
            ib -= 1;
            sum += (num[ib] as i64) - 48;
        }

        let mut sd: i64 = sum;
        let mut next_carry: i64 = 0;
        if sd >= 10 {
            sd -= 10;
            next_carry = 1;
        }

        if sd != cd {
            ok = false;
        } else {
            carry = next_carry;
        }
    }

    ok && carry == 0
}
