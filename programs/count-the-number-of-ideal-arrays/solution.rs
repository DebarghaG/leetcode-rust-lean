const MOD: i64 = 1_000_000_007;

pub fn ideal_arrays(n: i64, maxValue: i64) -> i64 {
    let m: usize = maxValue as usize;
    let n_usize: usize = n as usize;
    let max_k: usize = 20;
    let kk: usize = if n_usize < max_k { n_usize } else { max_k };

    let mut prev: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= m {
        prev.push(0);
        i += 1;
    }

    let mut v: usize = 1;
    while v <= m {
        prev[v] = 1;
        v += 1;
    }

    let mut comb: Vec<i64> = Vec::new();
    let mut c: usize = 0;
    while c <= kk {
        comb.push(0);
        c += 1;
    }
    comb[0] = 1;

    let total_gaps: usize = n_usize - 1;
    let mut i2: usize = 1;
    while i2 <= total_gaps {
        let upper: usize = if i2 < kk { i2 } else { kk };
        let mut r: usize = upper;
        while r > 0 {
            comb[r] = (comb[r] + comb[r - 1]) % MOD;
            r -= 1;
        }
        i2 += 1;
    }

    let mut ans: i64 = 0;
    let mut k: usize = 1;
    while k <= kk {
        let mut total: i64 = 0;
        let mut vv: usize = 1;
        while vv <= m {
            total += prev[vv];
            if total >= MOD {
                total -= MOD;
            }
            vv += 1;
        }

        let r_index: usize = k - 1;
        let choose: i64 = comb[r_index];
        ans = (ans + total * choose % MOD) % MOD;

        if k == kk {
            break;
        }

        let mut next: Vec<i64> = Vec::new();
        let mut z: usize = 0;
        while z <= m {
            next.push(0);
            z += 1;
        }

        let mut d: usize = 1;
        while d <= m {
            let val: i64 = prev[d];
            if val != 0 {
                let mut multiple: usize = d + d;
                while multiple <= m {
                    next[multiple] += val;
                    if next[multiple] >= MOD {
                        next[multiple] -= MOD;
                    }
                    multiple += d;
                }
            }
            d += 1;
        }

        prev = next;
        k += 1;
    }

    ans
}
