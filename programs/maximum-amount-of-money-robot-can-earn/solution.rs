pub fn maximum_amount(coins: &[Vec<i64>]) -> i64 {
    let m = coins.len();
    if m == 0 {
        return 0;
    }
    let n = coins[0].len();
    if n == 0 {
        return 0;
    }

    let w = n * 3;
    let neg: i64 = -1000000000000000000;

    let mut prev: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < m {
        let mut cur: Vec<i64> = Vec::new();
        while cur.len() < w {
            cur.push(neg);
        }

        let mut j = 0;
        while j < n {
            let c = coins[i][j];
            let base = j * 3;

            if i == 0 && j == 0 {
                cur[base] = c;
                if c < 0 {
                    cur[base + 1] = 0;
                }
            } else {
                let mut k = 0;
                while k < 3 {
                    let mut pred = neg;

                    if i > 0 {
                        let v = prev[base + k];
                        if v > pred {
                            pred = v;
                        }
                    }
                    if j > 0 {
                        let v = cur[base - 3 + k];
                        if v > pred {
                            pred = v;
                        }
                    }

                    let mut val = neg;
                    if pred != neg {
                        val = pred + c;
                    }

                    if c < 0 && k > 0 {
                        let mut pred2 = neg;

                        if i > 0 {
                            let v = prev[base + k - 1];
                            if v > pred2 {
                                pred2 = v;
                            }
                        }
                        if j > 0 {
                            let v = cur[base - 3 + k - 1];
                            if v > pred2 {
                                pred2 = v;
                            }
                        }

                        if pred2 > val {
                            val = pred2;
                        }
                    }

                    cur[base + k] = val;
                    k += 1;
                }
            }

            j += 1;
        }

        prev = cur;
        i += 1;
    }

    let last = (n - 1) * 3;
    let mut ans = prev[last];
    if prev[last + 1] > ans {
        ans = prev[last + 1];
    }
    if prev[last + 2] > ans {
        ans = prev[last + 2];
    }

    ans
}
