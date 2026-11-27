pub fn number_of_beautiful_integers(low: i64, high: i64, k: i64) -> i64 {
    count_leq(high, k) - count_leq(low - 1, k)
}

// Count completions of `remaining` free digits (each 0..=9) starting from
// diff-index `start_diff` and remainder `start_rem`, such that the final
// state has diff == cen (equal even/odd counts) and rem == 0 (divisible by k).
fn count_free(
    start_diff: usize,
    start_rem: usize,
    remaining: usize,
    width: usize,
    cen: usize,
    kk: usize,
) -> i64 {
    let size = width * kk;
    let mut dp: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < size {
        dp.push(0);
        i += 1;
    }
    let sidx = start_diff * kk + start_rem;
    dp[sidx] = dp[sidx] + 1;

    let mut step = 0usize;
    while step < remaining {
        let mut next: Vec<i64> = Vec::new();
        let mut j = 0usize;
        while j < size {
            next.push(0);
            j += 1;
        }

        let mut di = 0usize;
        while di < width {
            let mut r = 0usize;
            while r < kk {
                let cnt = dp[di * kk + r];
                if cnt != 0 {
                    let mut d = 0usize;
                    while d < 10 {
                        let mut valid = true;
                        let mut ndi = di;
                        if d % 2 == 0 {
                            if di + 1 < width {
                                ndi = di + 1;
                            } else {
                                valid = false;
                            }
                        } else {
                            if di > 0 {
                                ndi = di - 1;
                            } else {
                                valid = false;
                            }
                        }
                        if valid {
                            let nr = (r * 10 + d) % kk;
                            let nidx = ndi * kk + nr;
                            next[nidx] = next[nidx] + cnt;
                        }
                        d += 1;
                    }
                }
                r += 1;
            }
            di += 1;
        }

        dp = next;
        step += 1;
    }

    dp[cen * kk + 0]
}

// Count beautiful numbers with EXACTLY `l` digits (no leading zero),
// divisible by kk.
fn count_fixed_length(l: usize, kk: usize) -> i64 {
    if l == 0 {
        return 0;
    }
    let cen = l;
    let width = 2 * l + 1;
    let mut ans: i64 = 0;
    let mut d0 = 1usize;
    while d0 < 10 {
        let di: usize = if d0 % 2 == 0 { cen + 1 } else { cen - 1 };
        let r = d0 % kk;
        ans = ans + count_free(di, r, l - 1, width, cen, kk);
        d0 += 1;
    }
    ans
}

// Count beautiful numbers with EXACTLY `len` digits that are <= the
// number whose digits (LSB-first) are `digits`, divisible by kk.
fn count_tight(digits: &[i64], kk: usize) -> i64 {
    let len = digits.len();
    let cen = len;
    let width = 2 * len + 1;
    let mut ans: i64 = 0;

    let mut cur_di = cen;
    let mut cur_rem: usize = 0;
    let mut pos = 0usize;

    while pos < len {
        let digit = digits[len - 1 - pos];
        let digit_u = digit as usize;
        let lo: usize = if pos == 0 { 1 } else { 0 };

        let mut d = lo;
        while d < digit_u {
            let ndi: usize = if d % 2 == 0 { cur_di + 1 } else { cur_di - 1 };
            let nrem = (cur_rem * 10 + d) % kk;
            let remaining = len - pos - 1;
            ans = ans + count_free(ndi, nrem, remaining, width, cen, kk);
            d += 1;
        }

        // Continue along the tight path with d = digit.
        cur_di = if digit_u % 2 == 0 { cur_di + 1 } else { cur_di - 1 };
        cur_rem = (cur_rem * 10 + digit_u) % kk;
        pos += 1;
    }

    if cur_di == cen && cur_rem == 0 {
        ans = ans + 1;
    }
    ans
}

// Count beautiful integers in [1, n].
fn count_leq(n: i64, k: i64) -> i64 {
    if n <= 0 {
        return 0;
    }
    let kk = k as usize;

    let mut m = n;
    let mut digits: Vec<i64> = Vec::new();
    while m > 0 {
        digits.push(m % 10);
        m = m / 10;
    }
    let len = digits.len();

    let mut ans: i64 = 0;

    // All shorter lengths (only even lengths can be beautiful).
    let mut l = 2usize;
    while l < len {
        if l % 2 == 0 {
            ans = ans + count_fixed_length(l, kk);
        }
        l += 1;
    }

    // Numbers with exactly `len` digits, <= n.
    ans = ans + count_tight(&digits, kk);

    ans
}
