fn gcd_i64(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

pub fn count_different_subsequence_gc_ds(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    // For very small inputs, directly enumerate all non-empty subsequences.
    // This avoids any large vector sized by the maximum value.
    if n <= 12 {
        let total: usize = 1usize << n;
        let mut found: Vec<i64> = Vec::new();
        let mut mask: usize = 1;

        while mask < total {
            let mut g: i64 = 0;
            let mut i: usize = 0;

            while i < n {
                if ((mask >> i) & 1) == 1 {
                    g = gcd_i64(g, nums[i]);
                }
                i += 1;
            }

            let mut exists: bool = false;
            let mut k: usize = 0;
            while k < found.len() {
                if found[k] == g {
                    exists = true;
                    break;
                }
                k += 1;
            }

            if !exists {
                found.push(g);
            }

            mask += 1;
        }

        return found.len() as i64;
    }

    let mut max_val: usize = 0;
    let mut global_gcd: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let x = nums[i];
        let xu = x as usize;
        if xu > max_val {
            max_val = xu;
        }
        global_gcd = gcd_i64(global_gcd, x);
        i += 1;
    }

    let g_usize = global_gcd as usize;

    // For moderate n, aggregate directly by enumerating divisors of each value.
    // Work depends on n and sqrt(value), not on nested loops over all multiples.
    if n <= 4096 {
        let mut cur: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j <= max_val {
            cur.push(0);
            j += 1;
        }

        let mut idx: usize = 0;
        while idx < n {
            let x = nums[idx];
            let mut d: i64 = 1;

            while d <= x / d {
                if x % d == 0 {
                    if d % global_gcd == 0 {
                        let du = d as usize;
                        cur[du] = gcd_i64(cur[du], x);
                    }

                    let other = x / d;
                    if other != d && other % global_gcd == 0 {
                        let ou = other as usize;
                        cur[ou] = gcd_i64(cur[ou], x);
                    }
                }
                d += 1;
            }

            idx += 1;
        }

        let mut ans: i64 = 0;
        let mut d: usize = g_usize;

        while d <= max_val {
            if cur[d] == d as i64 {
                ans += 1;
            }
            d += g_usize;
        }

        return ans;
    }

    // For large n, use a presence array and scan multiples of each possible gcd.
    // Early stopping is safe: once the current gcd equals d, adding more multiples
    // of d cannot change it, since all remaining multiples are divisible by d.
    let mut present: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j <= max_val {
        present.push(0);
        j += 1;
    }

    i = 0;
    while i < n {
        let x = nums[i] as usize;
        present[x] = 1;
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut d: usize = g_usize;

    while d <= max_val {
        let d64 = d as i64;
        let mut cur: i64 = 0;
        let mut multiple: usize = d;

        while multiple <= max_val {
            if present[multiple] == 1 {
                cur = gcd_i64(cur, multiple as i64);
                if cur == d64 {
                    break;
                }
            }
            multiple += d;
        }

        if cur == d64 {
            ans += 1;
        }

        d += g_usize;
    }

    ans
}
