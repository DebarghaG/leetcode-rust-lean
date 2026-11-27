fn lower_bound(xs: &[i64], x: i64) -> i64 {
    let mut lo: i64 = 0;
    let mut hi: i64 = xs.len() as i64;
    while lo < hi {
        let mid = (lo + hi) / 2;
        if xs[mid as usize] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

pub fn maximum_triplet_value(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n < 3 {
        return 0;
    }

    // Coordinate compression of values.
    let mut vals: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        vals.push(nums[i]);
        i += 1;
    }
    vals.sort();

    let mut uniq: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < vals.len() {
        if uniq.len() == 0 || vals[i] != uniq[uniq.len() - 1] {
            uniq.push(vals[i]);
        }
        i += 1;
    }
    let m = uniq.len();

    let mut ranks: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        ranks.push(lower_bound(&uniq, nums[i]));
        i += 1;
    }

    // suffix[i] = maximum value in nums[i..n].
    let mut suffix: Vec<i64> = Vec::new();
    let mut i = 0;
    while i <= n {
        suffix.push(0);
        i += 1;
    }

    let mut i = n;
    while i > 0 {
        i -= 1;
        let mut best = suffix[i + 1];
        if nums[i] > best {
            best = nums[i];
        }
        suffix[i] = best;
    }

    // Fenwick tree for prefix maximum queries over compressed values.
    let mut tree: Vec<i64> = Vec::new();
    let mut i = 0;
    while i <= m {
        tree.push(0);
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut j = 0;
    while j < n {
        let rank = ranks[j] as usize;

        // Best nums[i] with i < j and nums[i] < nums[j].
        let mut q = rank;
        let mut left_best: i64 = 0;
        while q > 0 {
            if tree[q] > left_best {
                left_best = tree[q];
            }
            let low = q & (!q + 1);
            q -= low;
        }

        // Best nums[k] with k > j and nums[k] > nums[j].
        let right_best = suffix[j + 1];
        if left_best > 0 && right_best > nums[j] {
            let candidate = left_best - nums[j] + right_best;
            if candidate > ans {
                ans = candidate;
            }
        }

        // Insert nums[j] into the Fenwick tree.
        let mut p = rank + 1;
        while p <= m {
            if nums[j] > tree[p] {
                tree[p] = nums[j];
            }
            let low = p & (!p + 1);
            p += low;
        }

        j += 1;
    }

    ans
}
