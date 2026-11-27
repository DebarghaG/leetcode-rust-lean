pub fn minimum_time_required(jobs: &[i64], k: i64) -> i64 {
    let n = jobs.len();
    if n == 0 || k <= 0 {
        return 0;
    }

    let mut kk = k as usize;
    if kk > n {
        kk = n;
    }

    let mut a: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        a.push(jobs[i]);
        i += 1;
    }

    // Sort jobs in descending order using insertion sort.
    i = 1;
    while i < n {
        let val = a[i];
        let mut j = i;
        while j > 0 && a[j - 1] < val {
            a[j] = a[j - 1];
            j -= 1;
        }
        a[j] = val;
        i += 1;
    }

    if kk == 1 {
        let mut s = 0i64;
        i = 0;
        while i < n {
            s += a[i];
            i += 1;
        }
        return s;
    }

    if kk >= n {
        return a[0];
    }

    let mut total = 0i64;
    i = 0;
    while i < n {
        total += a[i];
        i += 1;
    }

    let k_i64 = kk as i64;
    let mut lower = a[0];
    let ceil = (total + k_i64 - 1) / k_i64;
    if ceil > lower {
        lower = ceil;
    }

    let mut loads: Vec<i64> = Vec::new();
    let mut w = 0usize;
    while w < kk {
        loads.push(0);
        w += 1;
    }

    // Greedy LPT gives an initial feasible upper bound.
    i = 0;
    while i < n {
        let mut minw = 0usize;
        let mut ww = 1usize;
        while ww < kk {
            if loads[ww] < loads[minw] {
                minw = ww;
            }
            ww += 1;
        }
        loads[minw] += a[i];
        i += 1;
    }

    let mut best = 0i64;
    w = 0;
    while w < kk {
        if loads[w] > best {
            best = loads[w];
        }
        w += 1;
    }

    if best == lower {
        return best;
    }

    w = 0;
    while w < kk {
        loads[w] = 0;
        w += 1;
    }

    let mut next_try: Vec<i64> = Vec::new();
    let mut assigned: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        next_try.push(0);
        assigned.push(0);
        i += 1;
    }

    let mut pos = 0usize;
    let mut done = false;

    while !done {
        let mut found = false;
        let mut chosen = 0usize;
        let mut ww = next_try[pos] as usize;

        while ww < kk && !found {
            let mut ok = true;

            if loads[ww] + a[pos] >= best {
                ok = false;
            }

            if ok {
                let mut p = 0usize;
                while p < ww {
                    if loads[p] == loads[ww] {
                        ok = false;
                    }
                    p += 1;
                }
            }

            if ok {
                found = true;
                chosen = ww;
                next_try[pos] = (ww + 1) as i64;
            } else {
                next_try[pos] = (ww + 1) as i64;
                ww += 1;
            }
        }

        if found {
            loads[chosen] += a[pos];
            assigned[pos] = chosen as i64;

            if pos + 1 == n {
                let mut maxload = 0i64;
                let mut q = 0usize;
                while q < kk {
                    if loads[q] > maxload {
                        maxload = loads[q];
                    }
                    q += 1;
                }

                if maxload < best {
                    best = maxload;
                }

                loads[chosen] -= a[pos];

                if best == lower {
                    return best;
                }
            } else {
                pos += 1;
                next_try[pos] = 0;
            }
        } else {
            if pos == 0 {
                done = true;
            } else {
                pos -= 1;
                let wprev = assigned[pos] as usize;
                loads[wprev] -= a[pos];
            }
        }
    }

    best
}
