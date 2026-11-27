fn value_mask(v: i64) -> i64 {
    if v == 2 {
        1
    } else if v == 3 {
        2
    } else if v == 5 {
        4
    } else if v == 6 {
        3
    } else if v == 7 {
        8
    } else if v == 10 {
        5
    } else if v == 11 {
        16
    } else if v == 13 {
        32
    } else if v == 14 {
        9
    } else if v == 15 {
        6
    } else if v == 17 {
        64
    } else if v == 19 {
        128
    } else if v == 21 {
        10
    } else if v == 22 {
        17
    } else if v == 23 {
        256
    } else if v == 26 {
        33
    } else if v == 29 {
        512
    } else if v == 30 {
        7
    } else {
        0
    }
}

pub fn number_of_good_subsets(nums: &[i64]) -> i64 {
    let modulus: i64 = 1000000007;

    let mut freq: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 31 {
        freq.push(0);
        i += 1;
    }

    let mut idx: usize = 0;
    while idx < nums.len() {
        let x = nums[idx];
        if x >= 1 && x <= 30 {
            let xi = x as usize;
            freq[xi] = freq[xi] + 1;
        }
        idx += 1;
    }

    let ones = freq[1];

    let mut dp: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 1024 {
        dp.push(0);
        k += 1;
    }
    dp[0] = 1;

    let mut v: i64 = 2;
    while v <= 30 {
        let m = value_mask(v);
        let c = freq[v as usize];

        if m != 0 && c > 0 {
            let mut mask: i64 = 1023;
            while mask >= 0 {
                if (mask & m) == 0 {
                    let mi = mask as usize;
                    let target = (mask | m) as usize;
                    let add = (dp[mi] * c) % modulus;
                    let new_val = (dp[target] + add) % modulus;
                    dp[target] = new_val;
                }
                mask = mask - 1;
            }
        }

        v = v + 1;
    }

    let mut total: i64 = 0;
    let mut mask2: usize = 1;
    while mask2 < 1024 {
        total = (total + dp[mask2]) % modulus;
        mask2 += 1;
    }

    let mut pow2: i64 = 1;
    let mut base: i64 = 2;
    let mut e: i64 = ones;
    while e > 0 {
        if e % 2 == 1 {
            pow2 = (pow2 * base) % modulus;
        }
        base = (base * base) % modulus;
        e = e / 2;
    }

    (total * pow2) % modulus
}
