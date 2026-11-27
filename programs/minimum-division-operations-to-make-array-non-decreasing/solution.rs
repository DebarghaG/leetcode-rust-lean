pub fn min_operations(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut maxv: i64 = 1;
    let mut idx: usize = 0;
    while idx < n {
        if nums[idx] > maxv {
            maxv = nums[idx];
        }
        idx += 1;
    }

    let m: usize = maxv as usize;
    let mut spf: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k <= m {
        spf.push(0);
        k += 1;
    }

    if m >= 1 {
        spf[1] = 1;
    }

    let mut i: usize = 2;
    while i <= m {
        if spf[i] == 0 {
            spf[i] = i as i64;
            if i <= m / i {
                let mut j: usize = i * i;
                while j <= m {
                    if spf[j] == 0 {
                        spf[j] = i as i64;
                    }
                    j += i;
                }
            }
        }
        i += 1;
    }

    let mut operations: i64 = 0;
    let mut bound: i64 = maxv;
    let mut ok: bool = true;
    let mut pos: usize = n;

    while pos > 0 && ok {
        pos -= 1;
        let x = nums[pos];
        if x <= bound {
            bound = x;
        } else {
            let reduced = spf[x as usize];
            if reduced < x && reduced <= bound {
                bound = reduced;
                operations += 1;
            } else {
                ok = false;
            }
        }
    }

    if !ok {
        return -1;
    }
    operations
}
