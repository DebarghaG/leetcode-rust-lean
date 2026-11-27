pub fn number_of_stable_arrays(zero: i64, one: i64, limit: i64) -> i64 {
    let modv: i64 = 1000000007;

    let nz: usize = zero as usize;
    let no: usize = one as usize;
    let lim: usize = limit as usize;

    let width: usize = no + 1;
    let size: usize = (nz + 1) * width;

    let mut dp0: Vec<i64> = Vec::new();
    let mut dp1: Vec<i64> = Vec::new();

    let mut t: usize = 0;
    while t < size {
        dp0.push(0);
        dp1.push(0);
        t += 1;
    }

    let mut i: usize = 1;
    while i <= nz && i <= lim {
        dp0[i * width] = 1;
        i += 1;
    }

    let mut j: usize = 1;
    while j <= no && j <= lim {
        dp1[j] = 1;
        j += 1;
    }

    i = 1;
    while i <= nz {
        j = 1;
        while j <= no {
            let mut sum0: i64 = 0;
            let mut k: usize = 1;
            while k <= lim && k <= i {
                let val = dp1[(i - k) * width + j];
                sum0 = (sum0 + val) % modv;
                k += 1;
            }
            dp0[i * width + j] = sum0;

            let mut sum1: i64 = 0;
            k = 1;
            while k <= lim && k <= j {
                let val = dp0[i * width + (j - k)];
                sum1 = (sum1 + val) % modv;
                k += 1;
            }
            dp1[i * width + j] = sum1;

            j += 1;
        }
        i += 1;
    }

    let last = nz * width + no;
    (dp0[last] + dp1[last]) % modv
}
