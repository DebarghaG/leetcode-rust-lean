fn gcd_i64(a0: i64, b0: i64) -> i64 {
    let mut a = a0;
    let mut b = b0;
    if a < 0 {
        a = -a;
    }
    if b < 0 {
        b = -b;
    }
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

fn mod_inv(a0: i64, m: i64) -> i64 {
    let mut old_r = a0 % m;
    let mut r = m;
    let mut old_s: i64 = 1;
    let mut s: i64 = 0;

    while r != 0 {
        let q = old_r / r;

        let tr = old_r - q * r;
        old_r = r;
        r = tr;

        let ts = old_s - q * s;
        old_s = s;
        s = ts;
    }

    let mut inv = old_s % m;
    if inv < 0 {
        inv += m;
    }
    inv
}

fn min_two_coins(a0: i64, b0: i64, amount: i64) -> i64 {
    let mut result: i64 = -1;

    if amount == 0 {
        return 0;
    }

    let mut big = a0;
    let mut small = b0;
    if big < small {
        let t = big;
        big = small;
        small = t;
    }

    if big > 0 && small > 0 {
        let g = gcd_i64(big, small);
        if amount % g == 0 {
            let ag = big / g;
            let bg = small / g;
            let target = amount / g;

            let inv = mod_inv(ag % bg, bg);
            let x0 = ((target % bg) * inv) % bg;

            let maxx = amount / big;
            if x0 <= maxx {
                let k = (maxx - x0) / bg;
                let x = x0 + k * bg;
                let rem = amount - big * x;

                if rem >= 0 && rem % small == 0 {
                    let y = rem / small;
                    result = x + y;
                }
            }
        }
    }

    result
}

pub fn coin_change(coins: &[i64], amount: i64) -> i64 {
    if amount < 0 {
        return -1;
    }
    if amount == 0 {
        return 0;
    }

    let mut raw: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < coins.len() {
        let c = coins[t];
        if c > 0 && c <= amount {
            raw.push(c);
        }
        t += 1;
    }

    if raw.len() == 0 {
        return -1;
    }

    // Sort descending.
    let mut i: usize = 1;
    while i < raw.len() {
        let v = raw[i];
        let mut j = i;
        while j > 0 && raw[j - 1] < v {
            raw[j] = raw[j - 1];
            j -= 1;
        }
        raw[j] = v;
        i += 1;
    }

    // Remove duplicates.
    let mut cs: Vec<i64> = Vec::new();
    t = 0;
    while t < raw.len() {
        if cs.len() == 0 || cs[cs.len() - 1] != raw[t] {
            cs.push(raw[t]);
        }
        t += 1;
    }

    // Check whether an exact single coin equals the amount.
    let mut has_exact: bool = false;
    t = 0;
    while t < cs.len() {
        if cs[t] == amount {
            has_exact = true;
        }
        t += 1;
    }
    if has_exact {
        return 1;
    }

    if cs.len() == 1 {
        if amount % cs[0] == 0 {
            return amount / cs[0];
        } else {
            return -1;
        }
    }

    if cs.len() == 2 {
        return min_two_coins(cs[0], cs[1], amount);
    }

    let n = cs.len();

    let mut g = cs[0];
    t = 1;
    while t < n {
        g = gcd_i64(g, cs[t]);
        t += 1;
    }
    if amount % g != 0 {
        return -1;
    }

    // suf[i] = gcd of cs[i], cs[i + 1], ..., cs[n - 1]
    let mut suf: Vec<i64> = Vec::new();
    t = 0;
    while t < n {
        suf.push(0);
        t += 1;
    }
    suf[n - 1] = cs[n - 1];
    t = n - 1;
    while t > 0 {
        t -= 1;
        suf[t] = gcd_i64(cs[t], suf[t + 1]);
    }

    let mut best = amount + 1;
    if cs[n - 1] == 1 {
        best = amount;
    }

    // Quick feasible upper bound (greedy).
    let mut grem = amount;
    let mut gcnt: i64 = 0;
    let mut gi: usize = 0;
    while gi < n {
        let take = grem / cs[gi];
        gcnt += take;
        grem -= take * cs[gi];
        gi += 1;
    }
    if grem == 0 && gcnt < best {
        best = gcnt;
    }

    let mut st_i: Vec<i64> = Vec::new();
    let mut st_rem: Vec<i64> = Vec::new();
    let mut st_cost: Vec<i64> = Vec::new();
    let mut st_next: Vec<i64> = Vec::new();

    st_i.push(0);
    st_rem.push(amount);
    st_cost.push(0);
    st_next.push(amount / cs[0]);

    let mut sp: usize = 1;

    while sp > 0 {
        let top = sp - 1;
        let idx_i = st_i[top] as usize;
        let rem = st_rem[top];
        let cost = st_cost[top];

        if rem == 0 {
            if cost < best {
                best = cost;
            }
            sp -= 1;
        } else if cost >= best {
            sp -= 1;
        } else if rem % suf[idx_i] != 0 {
            sp -= 1;
        } else if cost + (rem + cs[idx_i] - 1) / cs[idx_i] >= best {
            sp -= 1;
        } else if idx_i + 2 == n {
            let sub = min_two_coins(cs[idx_i], cs[idx_i + 1], rem);
            if sub >= 0 {
                let cand = cost + sub;
                if cand < best {
                    best = cand;
                }
            }
            sp -= 1;
        } else if idx_i + 1 == n {
            if rem % cs[idx_i] == 0 {
                let cand = cost + rem / cs[idx_i];
                if cand < best {
                    best = cand;
                }
            }
            sp -= 1;
        } else {
            let cnt = st_next[top];
            if cnt < 0 {
                sp -= 1;
            } else {
                st_next[top] = cnt - 1;

                let c = cs[idx_i];
                let newrem = rem - cnt * c;
                let newcost = cost + cnt;

                if newrem == 0 {
                    if newcost < best {
                        best = newcost;
                    }
                } else if newrem > 0 {
                    let nxt = cs[idx_i + 1];
                    let extra = (newrem + nxt - 1) / nxt;
                    if newcost + extra >= best {
                        sp -= 1;
                    } else if newrem % suf[idx_i + 1] != 0 {
                        // skip this branch, keep exploring siblings
                    } else if sp == st_i.len() {
                        st_i.push((idx_i + 1) as i64);
                        st_rem.push(newrem);
                        st_cost.push(newcost);
                        st_next.push(newrem / nxt);
                        sp += 1;
                    } else {
                        st_i[sp] = (idx_i + 1) as i64;
                        st_rem[sp] = newrem;
                        st_cost[sp] = newcost;
                        st_next[sp] = newrem / nxt;
                        sp += 1;
                    }
                }
            }
        }
    }

    if best > amount {
        -1
    } else {
        best
    }
}
