pub fn max_height(cuboids: &[Vec<i64>]) -> i64 {
    let n = cuboids.len();

    let mut a: Vec<i64> = Vec::new();
    let mut b: Vec<i64> = Vec::new();
    let mut c: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let row = &cuboids[i];
        let mut x = row[0];
        let mut y = row[1];
        let mut z = row[2];

        if x > y {
            let t = x;
            x = y;
            y = t;
        }
        if y > z {
            let t = y;
            y = z;
            z = t;
        }
        if x > y {
            let t = x;
            x = y;
            y = t;
        }

        a.push(x);
        b.push(y);
        c.push(z);

        i += 1;
    }

    // Sort triples (a, b, c) lexicographically with a simple bubble sort.
    let mut pass: usize = 0;
    while pass < n {
        let mut j: usize = 0;
        while j + 1 < n {
            let mut need_swap = false;

            if a[j] > a[j + 1] {
                need_swap = true;
            } else if a[j] == a[j + 1] {
                if b[j] > b[j + 1] {
                    need_swap = true;
                } else if b[j] == b[j + 1] {
                    if c[j] > c[j + 1] {
                        need_swap = true;
                    }
                }
            }

            if need_swap {
                let ta = a[j];
                a[j] = a[j + 1];
                a[j + 1] = ta;

                let tb = b[j];
                b[j] = b[j + 1];
                b[j + 1] = tb;

                let tc = c[j];
                c[j] = c[j + 1];
                c[j + 1] = tc;
            }

            j += 1;
        }

        pass += 1;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut ans: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let mut best = c[i];

        let mut j: usize = 0;
        while j < i {
            if a[j] <= a[i] && b[j] <= b[i] && c[j] <= c[i] {
                let candidate = dp[j] + c[i];
                if candidate > best {
                    best = candidate;
                }
            }
            j += 1;
        }

        dp.push(best);

        if best > ans {
            ans = best;
        }

        i += 1;
    }

    ans
}
