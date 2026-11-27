fn count_factor(mut x: i64, p: i64) -> i64 {
    let mut c = 0;
    while x > 1 && x % p == 0 {
        c += 1;
        x = x / p;
    }
    c
}

pub fn max_trailing_zeros(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }
    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let mut c2: Vec<Vec<i64>> = Vec::new();
    let mut c5: Vec<Vec<i64>> = Vec::new();

    let mut i = 0;
    while i < m {
        let row = &grid[i];
        let mut row2: Vec<i64> = Vec::new();
        let mut row5: Vec<i64> = Vec::new();

        let mut j = 0;
        while j < n {
            let x = row[j];
            row2.push(count_factor(x, 2));
            row5.push(count_factor(x, 5));
            j += 1;
        }

        c2.push(row2);
        c5.push(row5);
        i += 1;
    }

    let mut left2: Vec<Vec<i64>> = Vec::new();
    let mut left5: Vec<Vec<i64>> = Vec::new();

    i = 0;
    while i < m {
        let c2row = &c2[i];
        let c5row = &c5[i];

        let mut row2: Vec<i64> = Vec::new();
        let mut row5: Vec<i64> = Vec::new();

        let mut run2 = 0;
        let mut run5 = 0;

        let mut j = 0;
        while j < n {
            run2 += c2row[j];
            run5 += c5row[j];
            row2.push(run2);
            row5.push(run5);
            j += 1;
        }

        left2.push(row2);
        left5.push(row5);
        i += 1;
    }

    let mut up2: Vec<Vec<i64>> = Vec::new();
    let mut up5: Vec<Vec<i64>> = Vec::new();

    i = 0;
    while i < m {
        let c2row = &c2[i];
        let c5row = &c5[i];

        let mut row2: Vec<i64> = Vec::new();
        let mut row5: Vec<i64> = Vec::new();

        let mut j = 0;
        while j < n {
            let mut val2 = c2row[j];
            let mut val5 = c5row[j];

            if i > 0 {
                val2 += up2[i - 1][j];
                val5 += up5[i - 1][j];
            }

            row2.push(val2);
            row5.push(val5);
            j += 1;
        }

        up2.push(row2);
        up5.push(row5);
        i += 1;
    }

    let last2 = &up2[m - 1];
    let last5 = &up5[m - 1];

    let mut ans: i64 = 0;

    i = 0;
    while i < m {
        let l2row = &left2[i];
        let l5row = &left5[i];
        let u2row = &up2[i];
        let u5row = &up5[i];
        let c2row = &c2[i];
        let c5row = &c5[i];

        let row_total2 = l2row[n - 1];
        let row_total5 = l5row[n - 1];

        let mut j = 0;
        while j < n {
            let cell2 = c2row[j];
            let cell5 = c5row[j];

            let l2 = l2row[j];
            let l5 = l5row[j];

            let mut before2 = 0;
            let mut before5 = 0;
            if j > 0 {
                before2 = l2row[j - 1];
                before5 = l5row[j - 1];
            }

            let r2 = row_total2 - before2;
            let r5 = row_total5 - before5;

            let u2 = u2row[j];
            let u5 = u5row[j];

            let mut above2 = 0;
            let mut above5 = 0;
            if i > 0 {
                above2 = up2[i - 1][j];
                above5 = up5[i - 1][j];
            }

            let d2 = last2[j] - above2;
            let d5 = last5[j] - above5;

            let mut t2 = l2 + u2 - cell2;
            let mut t5 = l5 + u5 - cell5;
            let mut z = if t2 < t5 { t2 } else { t5 };
            if z > ans {
                ans = z;
            }

            t2 = l2 + d2 - cell2;
            t5 = l5 + d5 - cell5;
            z = if t2 < t5 { t2 } else { t5 };
            if z > ans {
                ans = z;
            }

            t2 = r2 + u2 - cell2;
            t5 = r5 + u5 - cell5;
            z = if t2 < t5 { t2 } else { t5 };
            if z > ans {
                ans = z;
            }

            t2 = r2 + d2 - cell2;
            t5 = r5 + d5 - cell5;
            z = if t2 < t5 { t2 } else { t5 };
            if z > ans {
                ans = z;
            }

            j += 1;
        }

        i += 1;
    }

    ans
}
