pub fn ways_to_split(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    if n < 3 {
        return 0;
    }

    let mut prefix: Vec<i64> = Vec::new();
    prefix.push(0);
    let mut k: usize = 0;
    while k < n {
        let next: i64 = prefix[k] + nums[k];
        prefix.push(next);
        k += 1;
    }
    let total: i64 = prefix[n];

    let mut vals: Vec<i64> = Vec::new();
    let mut j: usize = 1;
    while j < n {
        vals.push(prefix[j]);
        j += 1;
    }
    vals.sort();

    let mut unique: Vec<i64> = Vec::new();
    let mut ui: usize = 0;
    while ui < vals.len() {
        if unique.len() == 0 {
            unique.push(vals[ui]);
        } else {
            let last: i64 = unique[unique.len() - 1];
            if vals[ui] != last {
                unique.push(vals[ui]);
            }
        }
        ui += 1;
    }

    let m: usize = unique.len();
    let mut tree: Vec<i64> = Vec::new();
    let mut ti: usize = 0;
    while ti <= m {
        tree.push(0);
        ti += 1;
    }

    let rank_last: usize = lower_bound(&unique, prefix[n - 1]) + 1;
    let mut idx: usize = rank_last;
    while idx <= m {
        tree[idx] += 1;
        let low: usize = lowbit(idx);
        idx += low;
    }

    let mut ans: i64 = 0;
    let modv: i64 = 1000000007;
    let mut i: usize = n - 2;

    while i >= 1 {
        let p: i64 = prefix[i];
        let low_val: i64 = 2 * p;
        let loidx: usize = lower_bound(&unique, low_val);

        let target: i64 = total + p;
        let mut lo: usize = 0;
        let mut hi: usize = m;
        while lo < hi {
            let mid: usize = (lo + hi) / 2;
            if 2 * unique[mid] <= target {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let hiidx: usize = lo;

        if hiidx > loidx {
            let mut sum_hi: i64 = 0;
            let mut q: usize = hiidx;
            while q > 0 {
                sum_hi += tree[q];
                let low: usize = lowbit(q);
                q -= low;
            }

            let mut sum_lo: i64 = 0;
            let mut q2: usize = loidx;
            while q2 > 0 {
                sum_lo += tree[q2];
                let low2: usize = lowbit(q2);
                q2 -= low2;
            }

            let cnt: i64 = sum_hi - sum_lo;
            ans = (ans + cnt) % modv;
        }

        let rank_i: usize = lower_bound(&unique, p) + 1;
        let mut idx2: usize = rank_i;
        while idx2 <= m {
            tree[idx2] += 1;
            let low3: usize = lowbit(idx2);
            idx2 += low3;
        }

        i -= 1;
    }

    ans
}

fn lower_bound(vals: &[i64], target: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = vals.len();
    while lo < hi {
        let mid: usize = (lo + hi) / 2;
        if vals[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

fn lowbit(mut x: usize) -> usize {
    let mut low: usize = 1;
    while x > 1 && x % 2 == 0 {
        low *= 2;
        x /= 2;
    }
    low
}
