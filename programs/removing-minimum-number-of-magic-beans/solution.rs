pub fn minimum_removal(beans: &[i64]) -> i64 {
    let n = beans.len();
    if n == 0 {
        return 0;
    }

    let mut v: Vec<i64> = Vec::new();
    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let x = beans[i];
        v.push(x);
        total += x;
        i += 1;
    }

    let mut temp: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        temp.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    let mut from_v: bool = true;
    while width < n {
        let step = width + width;
        let mut left: usize = 0;

        if from_v {
            while left < n {
                let mut mid = left + width;
                if mid > n {
                    mid = n;
                }
                let mut right = left + step;
                if right > n {
                    right = n;
                }

                let mut a = left;
                let mut b = mid;
                let mut k = left;

                while a < mid && b < right {
                    if v[a] <= v[b] {
                        temp[k] = v[a];
                        a += 1;
                    } else {
                        temp[k] = v[b];
                        b += 1;
                    }
                    k += 1;
                }
                while a < mid {
                    temp[k] = v[a];
                    a += 1;
                    k += 1;
                }
                while b < right {
                    temp[k] = v[b];
                    b += 1;
                    k += 1;
                }

                left += step;
            }
            from_v = false;
        } else {
            while left < n {
                let mut mid = left + width;
                if mid > n {
                    mid = n;
                }
                let mut right = left + step;
                if right > n {
                    right = n;
                }

                let mut a = left;
                let mut b = mid;
                let mut k = left;

                while a < mid && b < right {
                    if temp[a] <= temp[b] {
                        v[k] = temp[a];
                        a += 1;
                    } else {
                        v[k] = temp[b];
                        b += 1;
                    }
                    k += 1;
                }
                while a < mid {
                    v[k] = temp[a];
                    a += 1;
                    k += 1;
                }
                while b < right {
                    v[k] = temp[b];
                    b += 1;
                    k += 1;
                }

                left += step;
            }
            from_v = true;
        }

        width = step;
    }

    let mut best: i64 = total;
    i = 0;

    if from_v {
        while i < n {
            let remaining = (n - i) as i64;
            let cost = total - v[i] * remaining;
            if cost < best {
                best = cost;
            }
            i += 1;
        }
    } else {
        while i < n {
            let remaining = (n - i) as i64;
            let cost = total - temp[i] * remaining;
            if cost < best {
                best = cost;
            }
            i += 1;
        }
    }

    best
}
