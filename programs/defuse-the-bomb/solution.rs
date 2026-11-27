pub fn decrypt(code: &[i64], k: i64) -> Vec<i64> {
    let n = code.len();
    let mut out: Vec<i64> = Vec::new();

    if n == 0 {
        return out;
    }

    if k == 0 {
        let mut i: usize = 0;
        while i < n {
            out.push(0);
            i += 1;
        }
        return out;
    }

    let n_i64 = n as i64;
    let mut i: usize = 0;

    if k > 0 {
        let m = k as usize;
        while i < n {
            let mut sum: i64 = 0;
            let mut d: usize = 1;
            while d <= m {
                let idx = (i + d) % n;
                sum += code[idx];
                d += 1;
            }
            out.push(sum);
            i += 1;
        }
    } else {
        let m = (0 - k) as usize;
        while i < n {
            let mut sum: i64 = 0;
            let mut d: usize = 1;
            while d <= m {
                let idx_i = i as i64 + n_i64 - d as i64;
                let mut idx_mod = idx_i % n_i64;
                if idx_mod < 0 {
                    idx_mod += n_i64;
                }
                let idx = idx_mod as usize;
                sum += code[idx];
                d += 1;
            }
            out.push(sum);
            i += 1;
        }
    }

    out
}
