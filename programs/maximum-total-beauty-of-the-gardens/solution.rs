fn sort_values(a: &mut Vec<i64>) {
    let n = a.len();
    if n < 2 {
        return;
    }

    let mut tmp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < n {
        tmp.push(0);
        z += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;
        while left < n {
            let mut mid: usize = left + width;
            if mid > n {
                mid = n;
            }
            let mut right: usize = left + width * 2;
            if right > n {
                right = n;
            }

            let mut i: usize = left;
            let mut j: usize = mid;
            let mut k: usize = left;

            while i < mid && j < right {
                if a[i] <= a[j] {
                    tmp[k] = a[i];
                    i += 1;
                } else {
                    tmp[k] = a[j];
                    j += 1;
                }
                k += 1;
            }
            while i < mid {
                tmp[k] = a[i];
                i += 1;
                k += 1;
            }
            while j < right {
                tmp[k] = a[j];
                j += 1;
                k += 1;
            }

            left = right;
        }

        let mut p: usize = 0;
        while p < n {
            a[p] = tmp[p];
            p += 1;
        }

        width = width * 2;
    }
}

pub fn maximum_beauty(
    flowers: &[i64],
    newFlowers: i64,
    target: i64,
    full: i64,
    partial: i64,
) -> i64 {
    let n = flowers.len();

    let mut a: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < n {
        a.push(flowers[idx]);
        idx += 1;
    }
    sort_values(&mut a);

    let mut pref: Vec<i64> = Vec::new();
    pref.push(0);
    let mut sum: i64 = 0;
    idx = 0;
    while idx < n {
        sum += a[idx];
        pref.push(sum);
        idx += 1;
    }

    let mut u: usize = 0;
    while u < n {
        if a[u] < target {
            u += 1;
        } else {
            break;
        }
    }

    let mut ans: i64 = 0;
    let mut i: usize = u;
    let mut cost_complete: i64 = 0;
    let mut go: bool = true;

    while go {
        if cost_complete <= newFlowers {
            let complete: i64 = (n - i) as i64;
            let rem: i64 = newFlowers - cost_complete;
            let mut best: i64 = 0;

            if i > 0 {
                let mut lo: usize = 1;
                let mut hi: usize = i;
                let mut p: usize = 1;

                while lo <= hi {
                    let mid: usize = lo + (hi - lo) / 2;
                    let cost: i64 = (mid as i64) * a[mid - 1] - pref[mid];

                    if cost <= rem {
                        p = mid;
                        lo = mid + 1;
                    } else {
                        hi = mid - 1;
                    }
                }

                best = (pref[p] + rem) / (p as i64);
                let cap: i64 = target - 1;
                if best > cap {
                    best = cap;
                }
            }

            let cand: i64 = complete * full + best * partial;
            if cand > ans {
                ans = cand;
            }
        }

        if i == 0 {
            go = false;
        } else {
            i -= 1;
            cost_complete += target - a[i];
            if cost_complete > newFlowers {
                go = false;
            }
        }
    }

    ans
}
