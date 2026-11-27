fn binom(n: i64, k: i64) -> i64 {
    if k < 0 {
        return 0;
    }
    if k > n {
        return 0;
    }

    let mut kk = k;
    if kk > n - kk {
        kk = n - kk;
    }

    let mut res: i64 = 1;
    let mut i: i64 = 1;
    while i <= kk {
        res = res * (n - kk + i);
        res = res / i;
        i = i + 1;
    }
    res
}

pub fn num_tile_possibilities(tiles: &[u8]) -> i64 {
    let n = tiles.len();

    let mut counts: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < 26 {
        counts.push(0);
        z = z + 1;
    }

    let mut i: usize = 0;
    while i < n {
        let idx = (tiles[i] as i64 - 65) as usize;
        counts[idx] = counts[idx] + 1;
        i = i + 1;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j <= n {
        dp.push(0);
        j = j + 1;
    }
    dp[0] = 1;

    let mut letter: usize = 0;
    while letter < 26 {
        let c = counts[letter];
        if c > 0 {
            let mut ndp: Vec<i64> = Vec::new();
            let mut q: usize = 0;
            while q <= n {
                ndp.push(0);
                q = q + 1;
            }

            let mut l: usize = 0;
            while l <= n {
                if dp[l] != 0 {
                    let mut t: i64 = 0;
                    while t <= c {
                        let nl: usize = l + (t as usize);
                        if nl <= n {
                            ndp[nl] = ndp[nl] + dp[l] * binom(nl as i64, t);
                        }
                        t = t + 1;
                    }
                }
                l = l + 1;
            }

            dp = ndp;
        }
        letter = letter + 1;
    }

    let mut ans: i64 = 0;
    let mut k: usize = 1;
    while k <= n {
        ans = ans + dp[k];
        k = k + 1;
    }
    ans
}
