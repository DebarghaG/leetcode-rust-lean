fn banned_sum_up_to(x: i64, bits: &[i64], sum_pref: &[i64]) -> i64 {
    if x <= 0 {
        return 0;
    }

    let xu: usize = x as usize;
    let q: usize = xu / 32;
    let rem: usize = xu % 32;

    let mut s: i64 = sum_pref[q];

    if rem > 0 {
        if q < bits.len() {
            let word: i64 = bits[q];
            let base: i64 = (q as i64) * 32;
            let mut j: usize = 0;
            while j < rem {
                let mask: i64 = 1i64 << j;
                if (word & mask) != 0 {
                    s += base + (j as i64) + 1;
                }
                j += 1;
            }
        }
    }

    s
}

fn banned_count_up_to(x: i64, bits: &[i64], cnt_pref: &[i64]) -> i64 {
    if x <= 0 {
        return 0;
    }

    let xu: usize = x as usize;
    let q: usize = xu / 32;
    let rem: usize = xu % 32;

    let mut c: i64 = cnt_pref[q];

    if rem > 0 {
        if q < bits.len() {
            let word: i64 = bits[q];
            let mut j: usize = 0;
            while j < rem {
                let mask: i64 = 1i64 << j;
                if (word & mask) != 0 {
                    c += 1;
                }
                j += 1;
            }
        }
    }

    c
}

pub fn max_count(banned: &[i64], n: i64, maxSum: i64) -> i64 {
    let n_usize: usize = n as usize;
    let num_words: usize = n_usize / 32 + 1;

    let mut bits: Vec<i64> = Vec::new();
    let mut block_count: Vec<i64> = Vec::new();
    let mut block_sum: Vec<i64> = Vec::new();

    let mut w: usize = 0;
    while w < num_words {
        bits.push(0);
        block_count.push(0);
        block_sum.push(0);
        w += 1;
    }

    let m: usize = banned.len();
    let mut i: usize = 0;
    while i < m {
        let b: i64 = banned[i];
        if b >= 1 && b <= n {
            let pos: usize = (b - 1) as usize;
            let word: usize = pos / 32;
            let shift: usize = pos % 32;
            let mask: i64 = 1i64 << shift;

            if (bits[word] & mask) == 0 {
                bits[word] = bits[word] | mask;
                block_count[word] += 1;
                block_sum[word] += b;
            }
        }
        i += 1;
    }

    let mut cnt_pref: Vec<i64> = Vec::new();
    let mut sum_pref: Vec<i64> = Vec::new();
    cnt_pref.push(0);
    sum_pref.push(0);

    w = 0;
    while w < num_words {
        let prev_c: i64 = cnt_pref[w];
        let prev_s: i64 = sum_pref[w];
        cnt_pref.push(prev_c + block_count[w]);
        sum_pref.push(prev_s + block_sum[w]);
        w += 1;
    }

    let mut lo: i64 = 0;
    let mut hi: i64 = n;

    while lo < hi {
        let mid: i64 = lo + (hi - lo + 1) / 2;
        let banned_s: i64 = banned_sum_up_to(mid, &bits, &sum_pref);
        let total: i64 = mid * (mid + 1) / 2;

        if total - banned_s <= maxSum {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }

    let banned_c: i64 = banned_count_up_to(lo, &bits, &cnt_pref);
    lo - banned_c
}
