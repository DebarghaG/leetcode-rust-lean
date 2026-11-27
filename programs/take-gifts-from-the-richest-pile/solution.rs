fn isqrt(n: i64) -> i64 {
    let mut lo: i64 = 0;
    let mut hi: i64 = n;
    let mut ans: i64 = 0;

    while lo <= hi {
        let mid: i64 = lo + (hi - lo) / 2;
        if mid * mid <= n {
            ans = mid;
            lo = mid + 1;
        } else {
            hi = mid - 1;
        }
    }

    ans
}

pub fn pick_gifts(gifts: &[i64], k: i64) -> i64 {
    let n = gifts.len();

    let mut piles: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        piles.push(gifts[i]);
        i += 1;
    }

    let mut second: i64 = 0;
    while second < k {
        let mut max_idx: usize = 0;
        let mut max_val: i64 = piles[0];

        let mut j: usize = 1;
        while j < n {
            if piles[j] > max_val {
                max_val = piles[j];
                max_idx = j;
            }
            j += 1;
        }

        piles[max_idx] = isqrt(piles[max_idx]);
        second += 1;
    }

    let mut total: i64 = 0;
    let mut t: usize = 0;
    while t < n {
        total += piles[t];
        t += 1;
    }

    total
}
