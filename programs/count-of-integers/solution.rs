const MOD: i64 = 1_000_000_007;

fn is_zero(s: &[u8]) -> bool {
    let mut i = 0;
    while i < s.len() {
        if s[i] != b'0' {
            return false;
        }
        i += 1;
    }
    true
}

fn dec_one(s: &[u8]) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < s.len() {
        v.push(s[i]);
        i += 1;
    }

    let mut j = v.len();
    while j > 0 {
        j -= 1;
        if v[j] > b'0' {
            v[j] = v[j] - 1;
            return v;
        } else {
            v[j] = b'9';
        }
    }

    v
}

fn count_leq(s: &[u8], min_sum: i64, max_sum: i64) -> i64 {
    if max_sum < 0 {
        return 0;
    }
    if min_sum > max_sum {
        return 0;
    }

    let max_usize = max_sum as usize;
    let width = max_usize + 1;
    let size = 2 * width;

    let mut dp: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < size {
        dp.push(0);
        i += 1;
    }

    // tight = 1 means the prefix is equal to s so far.
    // tight = 0 means the prefix is already smaller.
    dp[width] = 1;

    let n = s.len();
    let mut pos = 0;

    while pos < n {
        let limit = (s[pos] - b'0') as usize;

        let mut ndp: Vec<i64> = Vec::new();
        let mut k = 0;
        while k < size {
            ndp.push(0);
            k += 1;
        }

        let mut tight = 0;
        while tight < 2 {
            let mut sum = 0;
            while sum < width {
                let ways = dp[tight * width + sum];

                if ways != 0 {
                    let maxd = if tight == 1 { limit } else { 9 };

                    let mut d = 0;
                    while d <= maxd {
                        let ns = sum + d;

                        if ns < width {
                            let nt = if tight == 1 && d == limit { 1 } else { 0 };
                            let idx = nt * width + ns;
                            let cur = ndp[idx];
                            let nv = cur + ways;

                            if nv >= MOD {
                                ndp[idx] = nv - MOD;
                            } else {
                                ndp[idx] = nv;
                            }
                        }

                        d += 1;
                    }
                }

                sum += 1;
            }

            tight += 1;
        }

        dp = ndp;
        pos += 1;
    }

    let lo = if min_sum < 0 { 0 } else { min_sum as usize };

    let mut ans: i64 = 0;
    let mut tight = 0;
    while tight < 2 {
        let mut sum = lo;
        while sum < width {
            let v = dp[tight * width + sum];
            ans = ans + v;
            if ans >= MOD {
                ans = ans - MOD;
            }
            sum += 1;
        }
        tight += 1;
    }

    ans
}

pub fn count(num1: &[u8], num2: &[u8], min_sum: i64, max_sum: i64) -> i64 {
    let upper = count_leq(num2, min_sum, max_sum);

    let mut lower: i64 = 0;

    if is_zero(num1) {
        lower = 0;
    } else {
        let lower_num = dec_one(num1);
        lower = count_leq(&lower_num, min_sum, max_sum);
    }

    let mut ans = upper - lower;
    if ans < 0 {
        ans = ans + MOD;
    }

    ans
}
