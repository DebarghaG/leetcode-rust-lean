pub fn min_stickers(stickers: &[Vec<u8>], target: &[u8]) -> i64 {
    let n = target.len();
    if n == 0 {
        return 0;
    }

    let size: usize = 1usize << n;
    let inf: i64 = 1000000000;

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < size {
        dp.push(inf);
        i += 1;
    }
    dp[0] = 0;

    let s_count = stickers.len();
    let total_len: usize = s_count * 26;
    let mut counts: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < total_len {
        counts.push(0);
        t += 1;
    }

    let mut s: usize = 0;
    while s < s_count {
        let mut p: usize = 0;
        while p < stickers[s].len() {
            let idx = (stickers[s][p] as usize) - 97;
            counts[s * 26 + idx] += 1;
            p += 1;
        }
        s += 1;
    }

    let mut avail: Vec<i64> = Vec::new();
    let mut a: usize = 0;
    while a < 26 {
        avail.push(0);
        a += 1;
    }

    let mut mask: usize = 0;
    while mask < size {
        if dp[mask] < inf {
            let mut k: usize = 0;
            while k < s_count {
                let mut c: usize = 0;
                while c < 26 {
                    avail[c] = counts[k * 26 + c];
                    c += 1;
                }

                let mut next: usize = mask;
                let mut pos: usize = 0;
                while pos < n {
                    let bit: usize = 1usize << pos;
                    if (mask & bit) == 0 {
                        let ch = (target[pos] as usize) - 97;
                        if avail[ch] > 0 {
                            next = next | bit;
                            avail[ch] -= 1;
                        }
                    }
                    pos += 1;
                }

                if next != mask {
                    let cand = dp[mask] + 1;
                    if cand < dp[next] {
                        dp[next] = cand;
                    }
                }

                k += 1;
            }
        }
        mask += 1;
    }

    if dp[size - 1] == inf {
        -1
    } else {
        dp[size - 1]
    }
}
