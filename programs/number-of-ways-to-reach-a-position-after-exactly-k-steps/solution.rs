pub fn number_of_ways(startPos: i64, endPos: i64, k: i64) -> i64 {
    let md: i64 = 1000000007;

    if k < 0 {
        return 0;
    }

    let k_usize = k as usize;
    let n = k_usize * 2 + 1;

    let mut dp: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        dp.push(0);
        i += 1;
    }

    // The reachable window is [startPos - k, startPos + k].
    // startPos corresponds to offset k.
    dp[k_usize] = 1;

    let mut step = 0;
    while step < k_usize {
        let mut next: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            next.push(0);
            j += 1;
        }

        let mut idx = 0;
        while idx < n {
            let ways = dp[idx];
            if ways != 0 {
                if idx > 0 {
                    let mut v = next[idx - 1] + ways;
                    if v >= md {
                        v -= md;
                    }
                    next[idx - 1] = v;
                }

                if idx + 1 < n {
                    let mut v = next[idx + 1] + ways;
                    if v >= md {
                        v -= md;
                    }
                    next[idx + 1] = v;
                }
            }

            idx += 1;
        }

        dp = next;
        step += 1;
    }

    let end_offset_i64 = k + endPos - startPos;
    if end_offset_i64 < 0 {
        return 0;
    }

    let end_offset = end_offset_i64 as usize;
    if end_offset >= n {
        return 0;
    }

    dp[end_offset]
}
