fn floor_sqrt(n: i64) -> i64 {
    let mut r: i64 = 0;
    while (r + 1) * (r + 1) <= n {
        r += 1;
    }
    r
}

fn build_small_primes(limit: i64) -> Vec<i64> {
    let cap: usize = (limit + 1) as usize;
    let mut comp: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < cap {
        comp.push(false);
        i += 1;
    }
    let mut p: i64 = 2;
    while p * p <= limit {
        if !comp[p as usize] {
            let mut m: i64 = p * p;
            while m <= limit {
                comp[m as usize] = true;
                m += p;
            }
        }
        p += 1;
    }
    let mut primes: Vec<i64> = Vec::new();
    let mut q: i64 = 2;
    while q <= limit {
        if !comp[q as usize] {
            primes.push(q);
        }
        q += 1;
    }
    primes
}

pub fn closest_primes(left: i64, right: i64) -> Vec<i64> {
    let mut ans: Vec<i64> = Vec::new();

    // The gap of 1 is possible only between 2 and 3.
    if left <= 2 && right >= 3 {
        ans.push(2);
        ans.push(3);
        return ans;
    }

    let lo: i64 = if left < 2 { 2 } else { left };
    if lo > right {
        ans.push(-1);
        ans.push(-1);
        return ans;
    }

    let limit: i64 = floor_sqrt(right);
    let small_primes: Vec<i64> = build_small_primes(limit);

    // Segmented sieve over the range [lo, right], indexed by position.
    let n: usize = (right - lo + 1) as usize;
    let mut is_p: Vec<bool> = Vec::new();
    let mut f: usize = 0;
    while f < n {
        is_p.push(true);
        f += 1;
    }

    let mut k: usize = 0;
    while k < small_primes.len() {
        let p: i64 = small_primes[k];
        let mut start: i64 = p * p;
        if start < lo {
            let cc: i64 = (lo + p - 1) / p;
            start = cc * p;
        }
        let mut m: i64 = start;
        while m <= right {
            is_p[(m - lo) as usize] = false;
            m += p;
        }
        k += 1;
    }

    // Collect the primes lying in [lo, right].
    let mut plist: Vec<i64> = Vec::new();
    let mut c: usize = 0;
    while c < n {
        if is_p[c] {
            plist.push(lo + (c as i64));
        }
        c += 1;
    }

    if plist.len() < 2 {
        ans.push(-1);
        ans.push(-1);
        return ans;
    }

    // Minimum-gap tracking over consecutive primes (single-level branch body).
    let mut best_gap: i64 = right - lo + 2;
    let mut best1: i64 = -1;
    let mut best2: i64 = -1;
    let mut g: usize = 1;
    while g < plist.len() {
        let gap: i64 = plist[g] - plist[g - 1];
        if gap < best_gap {
            best_gap = gap;
            best1 = plist[g - 1];
            best2 = plist[g];
        }
        g += 1;
    }

    ans.push(best1);
    ans.push(best2);
    ans
}
