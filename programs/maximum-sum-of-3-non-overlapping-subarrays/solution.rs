pub fn max_sum_of_three_subarrays(nums: &[i64], k: i64) -> Vec<i64> {
    let mut res: Vec<i64> = Vec::new();
    if k <= 0 {
        return res;
    }
    let n = nums.len();
    let kk = k as usize;
    if 3 * kk > n {
        return res;
    }

    let m = n - kk + 1;

    // sums[i] = sum of nums[i .. i + kk]
    let mut sums: Vec<i64> = Vec::new();
    let mut s0: i64 = 0;
    let mut i: usize = 0;
    while i < kk {
        s0 += nums[i];
        i += 1;
    }
    sums.push(s0);

    let mut idx: usize = 1;
    while idx < m {
        let prev = sums[idx - 1];
        let new_val = prev - nums[idx - 1] + nums[idx + kk - 1];
        sums.push(new_val);
        idx += 1;
    }

    // rsum[i] = maximum of sums[j] for j >= i
    let mut rsum: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < m {
        rsum.push(0);
        t += 1;
    }

    let mut cur: usize = m;
    while cur > 0 {
        cur -= 1;
        if cur == m - 1 {
            rsum[cur] = sums[cur];
        } else {
            let here = sums[cur];
            let right = rsum[cur + 1];
            if here >= right {
                rsum[cur] = here;
            } else {
                rsum[cur] = right;
            }
        }
    }

    // pairval[p] = max over b >= p of sums[b] + rsum[b + kk]
    let bmax = m - 1 - kk;
    let mut pairval: Vec<i64> = Vec::new();
    let mut t2: usize = 0;
    while t2 < m {
        pairval.push(0);
        t2 += 1;
    }

    pairval[bmax] = sums[bmax] + rsum[bmax + kk];
    let mut p: usize = bmax;
    while p > 0 {
        p -= 1;
        let cand = sums[p] + rsum[p + kk];
        let right = pairval[p + 1];
        if cand >= right {
            pairval[p] = cand;
        } else {
            pairval[p] = right;
        }
    }

    // choose the smallest a that gives the global maximum sum
    let amax = m - 1 - 2 * kk;
    let mut best_total = sums[0] + pairval[kk];
    let mut best_a: usize = 0;
    let mut a: usize = 1;
    while a <= amax {
        let total = sums[a] + pairval[a + kk];
        if total > best_total {
            best_total = total;
            best_a = a;
        }
        a += 1;
    }

    // choose the smallest b that works with best_a
    let pstart = best_a + kk;
    let target = pairval[pstart];
    let mut b: usize = pstart;
    while b <= bmax {
        if sums[b] + rsum[b + kk] == target {
            break;
        }
        b += 1;
    }

    // choose the smallest c that works with b
    let mut c: usize = b + kk;
    let rtarget = rsum[b + kk];
    while c < m {
        if sums[c] == rtarget {
            break;
        }
        c += 1;
    }

    res.push(best_a as i64);
    res.push(b as i64);
    res.push(c as i64);
    res
}
