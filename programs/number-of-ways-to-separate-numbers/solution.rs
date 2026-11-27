pub fn number_of_combinations(num: &[u8]) -> i64 {
    let n = num.len();
    if n == 0 {
        return 0;
    }
    if num[0] == b'0' {
        return 0;
    }

    let modv: i64 = 1000000007;

    let mut prev_col: Vec<i64> = Vec::new();
    let mut curr_f: Vec<i64> = Vec::new();
    let mut total: Vec<i64> = Vec::new();
    let mut lcp: Vec<i64> = Vec::new();

    let mut t = 0usize;
    while t <= n {
        prev_col.push(0);
        curr_f.push(0);
        total.push(0);
        lcp.push(0);
        t += 1;
    }

    let mut j = 1usize;
    while j <= n {
        let mut run: i64 = 0;
        let mut a = n - j;
        while a > 0 {
            a -= 1;
            if num[a] == num[a + j] {
                run += 1;
            } else {
                run = 0;
            }
            lcp[a] = run;
        }

        let mut i = j;
        while i <= n {
            let mut f: i64 = 0;

            if i == j {
                f = 1;
            } else if num[i - j] == b'0' {
                f = 0;
            } else {
                let r = i - j;
                let mut sum: i64 = 0;

                if r < j - 1 {
                    sum = total[r];
                } else {
                    sum = prev_col[r];
                }

                if i >= 2 * j {
                    let a2 = i - 2 * j;
                    let l = lcp[a2];
                    let mut ok = false;

                    if l >= (j as i64) {
                        ok = true;
                    } else {
                        let p1 = a2 + (l as usize);
                        let p2 = a2 + j + (l as usize);
                        if num[p1] <= num[p2] {
                            ok = true;
                        }
                    }

                    if ok {
                        sum += curr_f[r];
                        if sum >= modv {
                            sum -= modv;
                        }
                    }
                }

                f = sum;
            }

            curr_f[i] = f;

            let mut g = prev_col[i] + f;
            if g >= modv {
                g -= modv;
            }

            if i == j {
                total[i] = g;
            }

            i += 1;
        }

        let mut i2 = j;
        while i2 <= n {
            let mut v = prev_col[i2] + curr_f[i2];
            if v >= modv {
                v -= modv;
            }
            prev_col[i2] = v;
            i2 += 1;
        }

        j += 1;
    }

    total[n]
}
