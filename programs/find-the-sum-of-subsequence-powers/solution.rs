const MOD: i64 = 1_000_000_007;

fn count_with_min_gap_at_least(a: &[i64], k: i64, d: i64) -> i64 {
    let n = a.len();

    if k <= 0 {
        return 0;
    }

    if k == 1 {
        let mut cnt: i64 = 0;
        let mut i = 0;
        while i < n {
            cnt += 1;
            i += 1;
        }
        return cnt % MOD;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        dp.push(1);
        i += 1;
    }

    let mut c: i64 = 2;
    while c <= k {
        let mut pref: Vec<i64> = Vec::new();
        pref.push(0);

        let mut j = 0;
        while j < n {
            let val = (pref[j] + dp[j]) % MOD;
            pref.push(val);
            j += 1;
        }

        let mut next: Vec<i64> = Vec::new();
        let mut p = 0;
        let mut idx = 0;

        while idx < n {
            while p < idx && a[p] <= a[idx] - d {
                p += 1;
            }
            next.push(pref[p]);
            idx += 1;
        }

        dp = next;
        c += 1;
    }

    let mut total = 0;
    let mut i = 0;
    while i < n {
        total = (total + dp[i]) % MOD;
        i += 1;
    }

    total
}

pub fn sum_of_powers(nums: &[i64], k: i64) -> i64 {
    if k < 2 {
        return 0;
    }

    let n = nums.len();

    let mut a: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }

    let mut i = 1;
    while i < n {
        let key = a[i];
        let mut j = i;
        while j > 0 && a[j - 1] > key {
            a[j] = a[j - 1];
            j -= 1;
        }
        a[j] = key;
        i += 1;
    }

    let mut raw: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        let mut j = i + 1;
        while j < n {
            let diff = a[j] - a[i];
            if diff > 0 {
                raw.push(diff);
            }
            j += 1;
        }
        i += 1;
    }

    let m = raw.len();
    if m == 0 {
        return 0;
    }

    let mut i = 1;
    while i < m {
        let key = raw[i];
        let mut j = i;
        while j > 0 && raw[j - 1] > key {
            raw[j] = raw[j - 1];
            j -= 1;
        }
        raw[j] = key;
        i += 1;
    }

    let mut ans = 0;
    let mut prev = 0;
    let mut idx = 0;

    while idx < m {
        let d = raw[idx];
        if d != prev {
            let f = count_with_min_gap_at_least(&a, k, d);
            let coef = (d - prev) % MOD;
            let term = (coef * f) % MOD;
            ans = (ans + term) % MOD;
            prev = d;
        }
        idx += 1;
    }

    ans
}
