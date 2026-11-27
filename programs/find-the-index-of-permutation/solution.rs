const MOD: i64 = 1_000_000_007;

pub fn get_permutation_index(perm: &[i64]) -> i64 {
    let n = perm.len();
    if n == 0 {
        return 0;
    }

    let mut fact: Vec<i64> = Vec::new();
    fact.push(1);

    let mut i: usize = 1;
    while i < n {
        let v = fact[i - 1] * (i as i64) % MOD;
        fact.push(v);
        i += 1;
    }

    let mut bit: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k <= n {
        bit.push(0);
        k += 1;
    }

    let mut val: usize = 1;
    while val <= n {
        let mut idx = val;
        while idx <= n {
            bit[idx] = bit[idx] + 1;
            let low = idx & (!idx + 1);
            idx += low;
        }
        val += 1;
    }

    let mut ans: i64 = 0;
    let mut pos: usize = 0;

    while pos < n {
        let x = perm[pos] as usize;

        let mut less: i64 = 0;
        let mut q = x - 1;
        while q > 0 {
            less += bit[q];
            let low = q & (!q + 1);
            q -= low;
        }

        let rem = n - 1 - pos;
        ans = (ans + less * fact[rem]) % MOD;

        let mut u = x;
        while u <= n {
            bit[u] = bit[u] - 1;
            let low = u & (!u + 1);
            u += low;
        }

        pos += 1;
    }

    ans
}
