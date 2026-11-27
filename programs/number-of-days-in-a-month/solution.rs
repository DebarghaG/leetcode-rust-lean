pub fn number_of_days(year: i64, month: i64) -> i64 {
    if month == 2 {
        if year % 400 == 0 || (year % 4 == 0 && year % 100 != 0) {
            29
        } else {
            28
        }
    } else if month == 4 || month == 6 || month == 9 || month == 11 {
        30
    } else {
        31
    }
}
