pub fn max_sum(nums: &[i64], k: i64) -> i64 {
    let modulus: i64 = 1000000007;
    let bits: usize = 63;

    let n = nums.len();

    let mut cnt: Vec<i64> = Vec::new();
    let mut b: usize = 0;
    while b < bits {
        cnt.push(0);
        b += 1;
    }

    let mut i: usize = 0;
    while i < n {
        let x = nums[i];
        b = 0;
        while b < bits {
            let mask = 1i64 << b;
            if (x & mask) != 0 {
                let old = cnt[b];
                cnt[b] = old + 1;
            }
            b += 1;
        }
        i += 1;
    }

    let kk: usize = k as usize;

    let mut vals: Vec<i64> = Vec::new();
    i = 0;
    while i < kk {
        vals.push(0);
        i += 1;
    }

    b = 0;
    while b < bits {
        let c = cnt[b];
        let mut limit: usize = kk;
        if c < k {
            limit = c as usize;
        }

        let add = (1i64 << b) % modulus;
        let mut j: usize = 0;
        while j < limit {
            let nv = vals[j] + add;
            if nv >= modulus {
                vals[j] = nv - modulus;
            } else {
                vals[j] = nv;
            }
            j += 1;
        }

        b += 1;
    }

    let mut ans: i64 = 0;
    i = 0;
    while i < kk {
        let v = vals[i];
        let sq = (v * v) % modulus;
        let na = ans + sq;
        if na >= modulus {
            ans = na - modulus;
        } else {
            ans = na;
        }
        i += 1;
    }

    ans
}
