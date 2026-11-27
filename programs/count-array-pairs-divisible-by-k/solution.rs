fn gcd_i64(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

pub fn count_pairs(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n < 2 {
        return 0;
    }

    let mut divisors: Vec<i64> = Vec::new();
    let mut d: i64 = 1;
    while d <= k {
        if k % d == 0 {
            divisors.push(d);
        }
        d += 1;
    }

    let m = divisors.len();
    let mut freq: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < m {
        freq.push(0);
        i += 1;
    }

    let mut idx: usize = 0;
    while idx < n {
        let g = gcd_i64(nums[idx], k);

        let mut j: usize = 0;
        while j < m {
            if divisors[j] == g {
                freq[j] = freq[j] + 1;
                j = m;
            } else {
                j += 1;
            }
        }

        idx += 1;
    }

    let mut ans: i64 = 0;
    let mut a_idx: usize = 0;

    while a_idx < m {
        let a = divisors[a_idx];
        let fa = freq[a_idx];

        if (a * a) % k == 0 {
            ans += fa * (fa - 1) / 2;
        }

        let mut b_idx: usize = a_idx + 1;
        while b_idx < m {
            let b = divisors[b_idx];
            if (a * b) % k == 0 {
                ans += fa * freq[b_idx];
            }
            b_idx += 1;
        }

        a_idx += 1;
    }

    ans
}
