fn gcd_i64(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    if a < 0 {
        -a
    } else {
        a
    }
}

fn lcm_i64(a: i64, b: i64) -> i64 {
    let g = gcd_i64(a, b);
    (a / g) * b
}

pub fn minimum_increments(nums: &[i64], target: &[i64]) -> i64 {
    let m = target.len();

    let mut total: usize = 1;
    let mut bi: usize = 0;
    while bi < m {
        total *= 2;
        bi += 1;
    }

    let mut lcms: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < total {
        lcms.push(1);
        i += 1;
    }

    let mut mask: usize = 1;
    while mask < total {
        let mut l: i64 = 1;
        let mut j: usize = 0;
        while j < m {
            let bit: usize = 1usize << j;
            if (mask & bit) != 0 {
                l = lcm_i64(l, target[j]);
            }
            j += 1;
        }
        lcms[mask] = l;
        mask += 1;
    }

    let inf: i64 = 1_000_000_000_000_000_000;

    let mut dp: Vec<i64> = Vec::new();
    i = 0;
    while i < total {
        dp.push(inf);
        i += 1;
    }
    dp[0] = 0;

    let n = nums.len();
    let mut idx: usize = 0;
    while idx < n {
        let x = nums[idx];

        let mut md: usize = total;
        while md > 0 {
            md -= 1;
            let curmask = md;

            if dp[curmask] < inf / 2 {
                let mut s: usize = 1;
                while s < total {
                    let newmask = curmask | s;
                    if newmask != curmask {
                        let l = lcms[s];
                        let r = x % l;
                        let cost = if r == 0 { 0 } else { l - r };
                        let cand = dp[curmask] + cost;
                        if cand < dp[newmask] {
                            dp[newmask] = cand;
                        }
                    }
                    s += 1;
                }
            }
        }

        idx += 1;
    }

    dp[total - 1]
}
