fn mod_pow(mut base: i64, mut exp: i64, modv: i64) -> i64 {
    let mut res: i64 = 1;
    base = base % modv;
    while exp > 0 {
        if exp % 2 == 1 {
            res = (res * base) % modv;
        }
        base = (base * base) % modv;
        exp = exp / 2;
    }
    res
}

pub fn ways_to_distribute(n: i64, k: i64) -> i64 {
    let modv: i64 = 1_000_000_007;

    if n < 0 || k < 0 {
        return 0;
    }
    if k > n {
        return 0;
    }
    if k == n {
        return 1;
    }
    if k == 0 {
        if n == 0 {
            return 1;
        }
        return 0;
    }
    if k == 1 {
        return 1;
    }

    let k_usize: usize = k as usize;

    // Compute k! modulo modv.
    let mut fact: i64 = 1;
    let mut i: i64 = 1;
    while i <= k {
        fact = (fact * i) % modv;
        i += 1;
    }

    // invfact[i] will store 1 / i! modulo modv.
    let mut invfact: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z <= k_usize {
        invfact.push(0);
        z += 1;
    }

    invfact[k_usize] = mod_pow(fact, modv - 2, modv);

    let mut idx: usize = k_usize;
    while idx > 0 {
        invfact[idx - 1] = (invfact[idx] * (idx as i64)) % modv;
        idx -= 1;
    }

    // Stirling number of the second kind:
    // S(n,k) = sum_{j=0}^k (-1)^(k-j) * j^n / (j! * (k-j)!).
    let mut sum: i64 = 0;
    let mut j: i64 = 0;
    while j <= k {
        let j_usize: usize = j as usize;
        let kj_usize: usize = (k - j) as usize;

        let coef: i64 = (invfact[j_usize] * invfact[kj_usize]) % modv;
        let power: i64 = mod_pow(j, n, modv);
        let term: i64 = (coef * power) % modv;

        if (k - j) % 2 == 1 {
            sum -= term;
            if sum < 0 {
                sum += modv;
            }
        } else {
            sum += term;
            if sum >= modv {
                sum -= modv;
            }
        }

        j += 1;
    }

    sum
}
