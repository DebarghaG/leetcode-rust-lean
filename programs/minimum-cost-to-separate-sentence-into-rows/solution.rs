pub fn minimum_cost(sentence: &[u8], k: i64) -> i64 {
    let n: usize = sentence.len();
    if n == 0 {
        return 0;
    }

    let mut lengths: Vec<i64> = Vec::new();
    let mut cur: i64 = 0;
    let mut p: usize = 0;

    while p < n {
        if sentence[p] == b' ' {
            lengths.push(cur);
            cur = 0;
        } else {
            cur = cur + 1;
        }
        p = p + 1;
    }
    lengths.push(cur);

    let m: usize = lengths.len();
    let mut dp: Vec<i64> = Vec::new();
    let mut idx: usize = 0;

    while idx <= m {
        dp.push(0);
        idx = idx + 1;
    }

    let inf: i64 = 1000000000000000000;
    let mut i: usize = m;

    while i > 0 {
        i = i - 1;

        let mut best: i64 = inf;
        let mut len_sum: i64 = 0;
        let mut j: usize = i;

        while j < m {
            if j > i {
                len_sum = len_sum + 1;
            }
            len_sum = len_sum + lengths[j];

            if len_sum > k {
                break;
            }

            let mut cand: i64 = 0;
            if j + 1 < m {
                let diff: i64 = k - len_sum;
                cand = diff * diff + dp[j + 1];
            }

            if cand < best {
                best = cand;
            }

            j = j + 1;
        }

        dp[i] = best;
    }

    dp[0]
}
