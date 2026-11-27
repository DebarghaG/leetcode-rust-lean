fn exists_ge(pos: usize, need_odd: i64, nd: &[i64], l: usize) -> bool {
    if pos > l {
        return false;
    }
    if need_odd < 0 {
        return false;
    }
    if need_odd > (l - pos) as i64 {
        return false;
    }
    if pos == l {
        return need_odd == 0;
    }

    let mut result = false;

    // Case 1: suffix exactly equals nd[pos..l].
    let mut equal_odds: i64 = 0;
    let mut i = pos;
    while i < l {
        if nd[i] % 2 == 1 {
            equal_odds += 1;
        }
        i += 1;
    }
    if equal_odds == need_odd {
        result = true;
    }

    // Case 2: first position i where the digit becomes strictly larger than nd[i].
    i = pos;
    let mut prefix_odds: i64 = 0;
    while i < l {
        let mut d = nd[i] + 1;
        while d <= 9 {
            let d_odd = d % 2;
            let rem_after = l - i - 1;
            let needed_after = need_odd - prefix_odds - d_odd;
            if needed_after >= 0 && needed_after <= rem_after as i64 {
                result = true;
            }
            d += 1;
        }
        if nd[i] % 2 == 1 {
            prefix_odds += 1;
        }
        i += 1;
    }

    result
}

fn can_finish(pos: usize, tight: bool, odd_used: i64, l: usize, nd: &[i64]) -> bool {
    if pos > l {
        return false;
    }

    let rem = l - pos;
    let target = (l as i64) / 2;
    let need = target - odd_used;

    if need < 0 {
        return false;
    }
    if need > rem as i64 {
        return false;
    }

    if !tight {
        return true;
    }

    if l > nd.len() {
        return false;
    }

    exists_ge(pos, need, nd, l)
}

pub fn closest_fair(n: i64) -> i64 {
    // Build decimal digits of n (big-endian).
    let mut rev: Vec<i64> = Vec::new();
    let mut temp = n;
    while temp > 0 {
        rev.push(temp % 10);
        temp = temp / 10;
    }

    let dlen = rev.len();
    let mut nd: Vec<i64> = Vec::new();
    let mut idx = dlen;
    while idx > 0 {
        idx -= 1;
        nd.push(rev[idx]);
    }

    // A fair integer must have an even number of digits.
    let mut l = dlen;
    if l % 2 != 0 {
        l += 1;
    }

    let mut answer: i64 = 0;
    let mut found = false;

    while !found {
        let target = (l as i64) / 2;
        let bound = l == dlen;

        let mut digits: Vec<i64> = Vec::new();
        let mut odd_used: i64 = 0;
        let mut tight = bound;
        let mut pos: usize = 0;
        let mut possible = true;

        while pos < l {
            let min_d: i64 = if pos == 0 { 1 } else { 0 };
            let mut chosen: i64 = -1;
            let mut d = min_d;

            while d <= 9 {
                if chosen < 0 {
                    let mut ok = true;
                    if tight && d < nd[pos] {
                        ok = false;
                    }
                    if ok {
                        let mut new_tight = false;
                        if tight && d == nd[pos] {
                            new_tight = true;
                        }
                        let new_odd = odd_used + (d % 2);
                        if new_odd <= target && can_finish(pos + 1, new_tight, new_odd, l, &nd) {
                            chosen = d;
                        }
                    }
                }
                if chosen < 0 {
                    d += 1;
                } else {
                    d = 10;
                }
            }

            if chosen < 0 {
                possible = false;
                pos = l;
            } else {
                digits.push(chosen);
                odd_used += chosen % 2;
                if tight && chosen > nd[pos] {
                    tight = false;
                }
                pos += 1;
            }
        }

        if possible && odd_used == target && digits.len() == l {
            let mut value: i64 = 0;
            let mut i = 0;
            while i < l {
                value = value * 10 + digits[i];
                i += 1;
            }
            answer = value;
            found = true;
        } else {
            l += 2;
        }
    }

    answer
}
