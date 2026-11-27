fn is_leap_year(y: i64) -> bool {
    if y % 400 == 0 {
        return true;
    }
    if y % 100 == 0 {
        return false;
    }
    if y % 4 == 0 {
        return true;
    }
    false
}

fn days_in_month(y: i64, m: i64) -> i64 {
    if m == 2 {
        if is_leap_year(y) {
            return 29;
        } else {
            return 28;
        }
    }
    if m == 4 || m == 6 || m == 9 || m == 11 {
        return 30;
    }
    31
}

fn days_since_1970(date: &[u8]) -> i64 {
    let y0 = (date[0] as i64) - 48;
    let y1 = (date[1] as i64) - 48;
    let y2 = (date[2] as i64) - 48;
    let y3 = (date[3] as i64) - 48;
    let year = y0 * 1000 + y1 * 100 + y2 * 10 + y3;

    let m0 = (date[5] as i64) - 48;
    let m1 = (date[6] as i64) - 48;
    let month = m0 * 10 + m1;

    let d0 = (date[8] as i64) - 48;
    let d1 = (date[9] as i64) - 48;
    let day = d0 * 10 + d1;

    let mut days: i64 = 0;

    let mut yr: i64 = 1970;
    while yr < year {
        if is_leap_year(yr) {
            days = days + 366;
        } else {
            days = days + 365;
        }
        yr = yr + 1;
    }

    let mut mo: i64 = 1;
    while mo < month {
        days = days + days_in_month(year, mo);
        mo = mo + 1;
    }

    days = days + day - 1;
    days
}

pub fn days_between_dates(date1: &[u8], date2: &[u8]) -> i64 {
    let d1 = days_since_1970(date1);
    let d2 = days_since_1970(date2);

    if d1 >= d2 {
        d1 - d2
    } else {
        d2 - d1
    }
}
