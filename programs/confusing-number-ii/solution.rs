fn pow5(k: usize) -> i64 {
    let mut result: i64 = 1;
    let mut i: usize = 0;
    while i < k {
        result = result * 5;
        i += 1;
    }
    result
}

fn is_valid_digit(d: i64) -> bool {
    d == 0 || d == 1 || d == 6 || d == 8 || d == 9
}

fn rotate_digit(d: i64) -> i64 {
    if d == 1 {
        1
    } else if d == 6 {
        9
    } else if d == 8 {
        8
    } else if d == 9 {
        6
    } else {
        0
    }
}

fn get_digits(n: i64) -> Vec<i64> {
    let mut digits: Vec<i64> = Vec::new();
    let mut temp = n;
    while temp > 0 {
        digits.push(temp % 10);
        temp = temp / 10;
    }

    let mut i: usize = 0;
    let mut j: usize = digits.len();
    while i < j {
        j -= 1;
        if i < j {
            let tmp = digits[i];
            digits[i] = digits[j];
            digits[j] = tmp;
        }
        i += 1;
    }
    digits
}

fn count_valid(n: i64) -> i64 {
    if n <= 0 {
        return 0;
    }

    let digits = get_digits(n);
    let m = digits.len();
    let mut ans: i64 = 0;

    let mut len: usize = 1;
    while len < m {
        ans += 4 * pow5(len - 1);
        len += 1;
    }

    let mut i: usize = 0;
    let mut matched: bool = true;
    while i < m && matched {
        let nd = digits[i];

        let mut d: i64 = 0;
        while d < nd {
            if is_valid_digit(d) && (i > 0 || d > 0) {
                ans += pow5(m - i - 1);
            }
            d += 1;
        }

        if is_valid_digit(nd) && (i > 0 || nd > 0) {
            i += 1;
        } else {
            matched = false;
        }
    }

    if matched {
        ans += 1;
    }

    ans
}

fn count_strobogrammatic(n: i64) -> i64 {
    if n <= 0 {
        return 0;
    }

    let digits = get_digits(n);
    let m = digits.len();
    let mut ans: i64 = 0;

    let mut len: usize = 1;
    while len < m {
        if len == 1 {
            ans += 2;
        } else {
            let pairs = len / 2;
            let mut count = 4 * pow5(pairs - 1);
            if len % 2 == 1 {
                count = count * 3;
            }
            ans += count;
        }
        len += 1;
    }

    if m == 1 {
        let nd = digits[0];
        let mut d: i64 = 1;
        while d <= nd {
            if d == 1 || d == 8 {
                ans += 1;
            }
            d += 1;
        }
    } else {
        let pairs: usize = m / 2;
        let has_mid: bool = (m % 2) == 1;
        let mut half: usize = pairs;
        if has_mid {
            half = half + 1;
        }

        let mut i: usize = 0;
        let mut matched: bool = true;

        while i < half && matched {
            let nd = digits[i];

            let mut completions: i64 = 1;
            if has_mid && i < pairs {
                completions = pow5(pairs - i - 1) * 3;
            } else if !has_mid && i < pairs {
                completions = pow5(pairs - i - 1);
            }

            let mut d: i64 = 0;
            while d < nd {
                let mut allowed: bool = false;

                if i == 0 {
                    if d == 1 || d == 6 || d == 8 || d == 9 {
                        allowed = true;
                    }
                } else if has_mid && i == pairs {
                    if d == 0 || d == 1 || d == 8 {
                        allowed = true;
                    }
                } else {
                    if d == 0 || d == 1 || d == 6 || d == 8 || d == 9 {
                        allowed = true;
                    }
                }

                if allowed {
                    ans += completions;
                }

                d += 1;
            }

            let mut nd_ok: bool = false;

            if i == 0 {
                if nd == 1 || nd == 6 || nd == 8 || nd == 9 {
                    nd_ok = true;
                }
            } else if has_mid && i == pairs {
                if nd == 0 || nd == 1 || nd == 8 {
                    nd_ok = true;
                }
            } else {
                if nd == 0 || nd == 1 || nd == 6 || nd == 8 || nd == 9 {
                    nd_ok = true;
                }
            }

            if nd_ok {
                i += 1;
            } else {
                matched = false;
            }
        }

        if matched {
            let mut value: i64 = 0;
            let mut pos: usize = 0;

            while pos < m {
                let mut dig: i64 = 0;

                if pos < half {
                    dig = digits[pos];
                } else {
                    let src: usize = m - 1 - pos;
                    dig = rotate_digit(digits[src]);
                }

                value = value * 10 + dig;
                pos += 1;
            }

            if value <= n {
                ans += 1;
            }
        }
    }

    ans
}

pub fn confusing_number_ii(n: i64) -> i64 {
    if n <= 0 {
        return 0;
    }

    let valid = count_valid(n);
    let not_confusing = count_strobogrammatic(n);
    valid - not_confusing
}
