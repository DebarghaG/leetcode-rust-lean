fn ascii_digit(b: u8) -> i64 {
    if b == 48 {
        return 0;
    }
    if b == 49 {
        return 1;
    }
    if b == 50 {
        return 2;
    }
    if b == 51 {
        return 3;
    }
    if b == 52 {
        return 4;
    }
    if b == 53 {
        return 5;
    }
    if b == 54 {
        return 6;
    }
    if b == 55 {
        return 7;
    }
    if b == 56 {
        return 8;
    }
    return 9;
}

pub fn day_of_year(date: &[u8]) -> i64 {
    let y0: i64 = ascii_digit(date[0]);
    let y1: i64 = ascii_digit(date[1]);
    let y2: i64 = ascii_digit(date[2]);
    let y3: i64 = ascii_digit(date[3]);
    let year: i64 = ((y0 * 10 + y1) * 10 + y2) * 10 + y3;

    let month: i64 = ascii_digit(date[5]) * 10 + ascii_digit(date[6]);
    let day: i64 = ascii_digit(date[8]) * 10 + ascii_digit(date[9]);

    let mut leap: bool = false;
    if year % 4 == 0 {
        leap = true;
    }
    if year % 100 == 0 {
        leap = false;
    }
    if year % 400 == 0 {
        leap = true;
    }

    let mut total: i64 = 0;
    let mut m: i64 = 1;
    while m < month {
        let mut dim: i64 = 31;
        if m == 4 {
            dim = 30;
        }
        if m == 6 {
            dim = 30;
        }
        if m == 9 {
            dim = 30;
        }
        if m == 11 {
            dim = 30;
        }
        if m == 2 {
            if leap {
                dim = 29;
            } else {
                dim = 28;
            }
        }
        total = total + dim;
        m = m + 1;
    }

    total + day
}
