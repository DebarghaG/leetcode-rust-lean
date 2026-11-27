pub fn sum_of_floored_pairs(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    if n == 0 {
        return 0;
    }

    let modv: i64 = 1000000007;

    // For small inputs, direct evaluation is both simple and fast.
    if n <= 128 {
        let mut ans: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let x: i64 = nums[i];
            let mut j: usize = 0;
            while j < n {
                let d: i64 = nums[j];
                if d > 0 {
                    ans = (ans + x / d) % modv;
                }
                j += 1;
            }
            i += 1;
        }
        return ans;
    }

    // Copy and sort the input.  All later work is indexed by positions in
    // this sorted vector, not by the numeric values themselves.
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }
    a.sort();

    // Compress equal values.
    let mut vals: Vec<i64> = Vec::new();
    let mut cnts: Vec<i64> = Vec::new();

    i = 0;
    while i < n {
        let v: i64 = a[i];
        let mut c: i64 = 1;
        let mut k: usize = i + 1;
        while k < n && a[k] == v {
            c += 1;
            k += 1;
        }
        vals.push(v);
        cnts.push(c);
        i = k;
    }

    let u: usize = vals.len();
    let u_i: i64 = u as i64;
    let maxv: i64 = vals[u - 1];

    // pref[t] = number of original elements with compressed value index < t.
    let mut pref: Vec<i64> = Vec::new();
    pref.push(0);
    let mut running: i64 = 0;
    let mut idx: usize = 0;
    while idx < u {
        running += cnts[idx];
        pref.push(running);
        idx += 1;
    }

    let mut ans: i64 = 0;
    let mut di: usize = 0;

    while di < u {
        let d: i64 = vals[di];
        let cd: i64 = cnts[di];
        let maxk: i64 = maxv / d;

        let mut f: i64 = 0;

        // Choose between scanning all distinct values and scanning multiples
        // of d.  This keeps both small-n and large-value cases fast.
        if u_i <= maxk * 2 {
            let mut vi: usize = 0;
            while vi < u {
                let v: i64 = vals[vi];
                f += (v / d) * cnts[vi];
                vi += 1;
            }
        } else {
            let mut kk: i64 = 1;
            while kk <= maxk {
                let threshold: i64 = kk * d;

                // lower_bound over vals for threshold
                let mut lo: usize = 0;
                let mut hi: usize = u;
                while lo < hi {
                    let mid: usize = (lo + hi) / 2;
                    if vals[mid] < threshold {
                        lo = mid + 1;
                    } else {
                        hi = mid;
                    }
                }

                // Number of elements >= threshold.
                let ge: i64 = n as i64 - pref[lo];
                f += ge;
                kk += 1;
            }
        }

        let term: i64 = (cd % modv) * (f % modv) % modv;
        ans = (ans + term) % modv;
        di += 1;
    }

    ans
}
