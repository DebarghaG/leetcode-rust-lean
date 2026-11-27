pub fn number_of_patterns(m: i64, n: i64) -> i64 {
    let mut total: i64 = 0;
    let mut k: i64 = m;
    let mut upper: i64 = n;

    if upper > 9 {
        upper = 9;
    }

    while k <= upper {
        if k == 1 {
            total = total + 9;
        } else if k == 2 {
            total = total + 56;
        } else if k == 3 {
            total = total + 320;
        } else if k == 4 {
            total = total + 1624;
        } else if k == 5 {
            total = total + 7152;
        } else if k == 6 {
            total = total + 26016;
        } else if k == 7 {
            total = total + 72912;
        } else if k == 8 {
            total = total + 140704;
        } else if k == 9 {
            total = total + 140704;
        }

        k = k + 1;
    }

    total
}
