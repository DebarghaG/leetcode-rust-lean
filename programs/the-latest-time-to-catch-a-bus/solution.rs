pub fn latest_time_catch_the_bus(buses: &[i64], passengers: &[i64], capacity: i64) -> i64 {
    let mut bs: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < buses.len() {
        bs.push(buses[i]);
        i += 1;
    }
    sort_i64(&mut bs);

    let mut ps: Vec<i64> = Vec::new();
    i = 0;
    while i < passengers.len() {
        ps.push(passengers[i]);
        i += 1;
    }
    sort_i64(&mut ps);

    let n = bs.len();
    let m = ps.len();
    let cap = capacity;

    let mut idx: usize = 0;
    let mut last_boarded: i64 = 0;
    let mut last_bus_full: bool = false;

    let mut bus_i: usize = 0;
    while bus_i < n {
        let bus = bs[bus_i];
        let mut count: i64 = 0;

        while idx < m && ps[idx] <= bus && count < cap {
            last_boarded = ps[idx];
            idx += 1;
            count += 1;
        }

        if bus_i + 1 == n {
            if count < cap {
                last_bus_full = false;
            } else {
                last_bus_full = true;
            }
        }

        bus_i += 1;
    }

    let mut ans: i64;
    if last_bus_full {
        ans = last_boarded - 1;
    } else {
        ans = bs[n - 1];
    }

    let mut j: usize = m;
    while j > 0 {
        j -= 1;
        if ps[j] == ans {
            ans -= 1;
        } else if ps[j] < ans {
            break;
        }
    }

    ans
}

fn sort_i64(v: &mut Vec<i64>) {
    let n = v.len();
    if n <= 1 {
        return;
    }

    let mut tmp: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < n {
        tmp.push(0);
        t += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut start: usize = 0;

        while start < n {
            let mut mid = start + width;
            if mid > n {
                mid = n;
            }

            let mut end = start + width + width;
            if end > n {
                end = n;
            }

            let mut l = start;
            let mut r = mid;
            let mut k = start;

            while l < mid && r < end {
                if v[l] <= v[r] {
                    tmp[k] = v[l];
                    l += 1;
                } else {
                    tmp[k] = v[r];
                    r += 1;
                }
                k += 1;
            }

            while l < mid {
                tmp[k] = v[l];
                l += 1;
                k += 1;
            }

            while r < end {
                tmp[k] = v[r];
                r += 1;
                k += 1;
            }

            start = end;
        }

        let mut j: usize = 0;
        while j < n {
            v[j] = tmp[j];
            j += 1;
        }

        width = width + width;
    }
}
