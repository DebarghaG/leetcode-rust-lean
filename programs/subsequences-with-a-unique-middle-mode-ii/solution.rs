const MOD: i64 = 1_000_000_007;

fn norm_mod(x: i64) -> i64 {
    let r = x % MOD;
    if r < 0 { r + MOD } else { r }
}

fn add_mod(a: i64, b: i64) -> i64 {
    norm_mod(a + b)
}

fn sub_mod(a: i64, b: i64) -> i64 {
    norm_mod(a - b)
}

fn mul_mod(a: i64, b: i64) -> i64 {
    norm_mod((a % MOD) * (b % MOD))
}

fn comb2(x: i64) -> i64 {
    if x < 2 {
        0
    } else {
        ((x * (x - 1)) / 2) % MOD
    }
}

fn lower_bound(vals: &[i64], x: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = vals.len();
    while lo < hi {
        let mid = (lo + hi) / 2;
        if vals[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

pub fn subsequences_with_middle_mode(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n < 5 {
        return 0;
    }

    let mut sorted: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        sorted.push(nums[i]);
        i = i + 1;
    }
    sorted.sort();

    let mut uniq: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        if i == 0 || sorted[i] != sorted[i - 1] {
            uniq.push(sorted[i]);
        }
        i = i + 1;
    }

    let m = uniq.len();
    let uniq_slice: &[i64] = &uniq;

    let mut arr: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        let idx = lower_bound(uniq_slice, nums[i]);
        arr.push(idx as i64);
        i = i + 1;
    }

    let mut cL: Vec<i64> = Vec::new();
    let mut cR: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < m {
        cL.push(0);
        cR.push(0);
        j = j + 1;
    }

    i = 0;
    while i < n {
        let v = arr[i] as usize;
        cR[v] = cR[v] + 1;
        i = i + 1;
    }

    let mut sumC2L: i64 = 0;
    let mut sumC2R: i64 = 0;

    j = 0;
    while j < m {
        sumC2R = add_mod(sumC2R, comb2(cR[j]));
        j = j + 1;
    }

    let mut a_sum: i64 = 0;
    let mut b_sum: i64 = 0;
    let mut c_sum: i64 = 0;
    let mut ans: i64 = 0;

    i = 0;
    while i < n {
        let v = arr[i] as usize;
        let l = cL[v];
        let old_r = cR[v];

        cR[v] = old_r - 1;

        sumC2R = sub_mod(sumC2R, comb2(old_r));
        sumC2R = add_mod(sumC2R, comb2(old_r - 1));

        a_sum = sub_mod(a_sum, l);
        b_sum = sub_mod(b_sum, mul_mod(l, 2 * old_r - 1));
        c_sum = sub_mod(c_sum, mul_mod(l, l));

        let la = l;
        let ra = cR[v];

        let ltot = i as i64;
        let rtot = (n - 1 - i) as i64;
        let lnon = ltot - la;
        let rnon = rtot - ra;

        let c_ltot = comb2(ltot);
        let c_rtot = comb2(rtot);
        let c_lnon = comb2(lnon);
        let c_rnon = comb2(rnon);

        let total = mul_mod(c_ltot, c_rtot);
        let k0 = mul_mod(c_lnon, c_rnon);

        let term1 = mul_mod(mul_mod(la, lnon), c_rnon);
        let term2 = mul_mod(mul_mod(ra, rnon), c_lnon);
        let k1 = add_mod(term1, term2);

        let sumR_ex = sub_mod(sumC2R, comb2(ra));
        let dR = sub_mod(c_rnon, sumR_ex);

        let sumL_ex = sub_mod(sumC2L, comb2(la));
        let dL = sub_mod(c_lnon, sumL_ex);

        let la_ra = mul_mod(la, ra);
        let a_ex = sub_mod(a_sum, la_ra);
        let b_ex = sub_mod(b_sum, mul_mod(la_ra, ra));
        let c_ex = sub_mod(c_sum, mul_mod(mul_mod(la, la), ra));

        let qR = sub_mod(mul_mod(rnon, a_ex), b_ex);
        let fR = sub_mod(mul_mod(dR, lnon), qR);

        let qL = sub_mod(mul_mod(lnon, a_ex), c_ex);
        let fL = sub_mod(mul_mod(dL, rnon), qL);

        let valid_k1 = add_mod(mul_mod(la, fR), mul_mod(ra, fL));

        let mut contrib = sub_mod(total, k0);
        contrib = sub_mod(contrib, k1);
        contrib = add_mod(contrib, valid_k1);

        ans = add_mod(ans, contrib);

        cL[v] = l + 1;
        sumC2L = add_mod(sumC2L, l);

        let rv = cR[v];
        a_sum = add_mod(a_sum, rv);
        b_sum = add_mod(b_sum, mul_mod(rv, rv));
        c_sum = add_mod(c_sum, mul_mod(2 * l + 1, rv));

        i = i + 1;
    }

    ans
}
