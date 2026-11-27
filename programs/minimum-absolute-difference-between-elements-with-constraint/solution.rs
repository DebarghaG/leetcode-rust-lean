pub fn min_absolute_difference(nums: &[i64], x: i64) -> i64 {
    if x <= 0 {
        return 0;
    }

    let n = nums.len();
    let xx = x as usize;

    // Copy values for coordinate compression.
    let mut vals: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        vals.push(nums[i]);
        i += 1;
    }

    // Iterative bottom-up merge sort.
    let vn = vals.len();
    let mut tmp: Vec<i64> = Vec::new();
    i = 0;
    while i < vn {
        tmp.push(0);
        i += 1;
    }

    let mut width = 1usize;
    while width < vn {
        let mut start = 0usize;
        while start < vn {
            let mid = if start + width < vn { start + width } else { vn };
            let end = if start + 2 * width < vn { start + 2 * width } else { vn };

            let mut left = start;
            let mut right = mid;
            let mut out = start;

            while left < mid && right < end {
                if vals[left] <= vals[right] {
                    tmp[out] = vals[left];
                    left += 1;
                } else {
                    tmp[out] = vals[right];
                    right += 1;
                }
                out += 1;
            }
            while left < mid {
                tmp[out] = vals[left];
                left += 1;
                out += 1;
            }
            while right < end {
                tmp[out] = vals[right];
                right += 1;
                out += 1;
            }

            start += 2 * width;
        }

        i = 0;
        while i < vn {
            vals[i] = tmp[i];
            i += 1;
        }

        width = width * 2;
    }

    // Deduplicate sorted values.
    let mut uniq: Vec<i64> = Vec::new();
    uniq.push(vals[0]);
    i = 1;
    while i < vn {
        if vals[i] != vals[i - 1] {
            uniq.push(vals[i]);
        }
        i += 1;
    }

    let m = uniq.len();

    // Fenwick tree storing counts of inserted compressed values.
    let mut bit: Vec<i64> = Vec::new();
    i = 0;
    while i <= m {
        bit.push(0);
        i += 1;
    }

    let mut ans: i64 = 2000000000;
    let mut j = xx;
    let mut total: i64 = 0;

    while j < n {
        // Insert nums[j - xx].
        let inserted = nums[j - xx];
        let idx_ins = lower_bound(&uniq, inserted);

        let mut p = idx_ins + 1;
        while p <= m {
            bit[p] = bit[p] + 1;
            let lb = p & (p ^ (p - 1));
            p = p + lb;
        }
        total += 1;

        let q = nums[j];
        let pos = lower_bound(&uniq, q);

        // Predecessor among inserted values: largest value <= q.
        let mut has_pre = false;
        let mut pre_pos = 0usize;
        if pos < m && uniq[pos] == q {
            has_pre = true;
            pre_pos = pos;
        } else if pos > 0 {
            has_pre = true;
            pre_pos = pos - 1;
        }

        if has_pre {
            let cnt = fenwick_prefix(&bit, pre_pos + 1);
            if cnt > 0 {
                let idx = fenwick_kth(&bit, m, cnt);
                let diff = q - uniq[idx];
                if diff < ans {
                    ans = diff;
                }
            }
        }

        // Successor among inserted values: smallest value >= q.
        if pos < m {
            let cnt_before = fenwick_prefix(&bit, pos);
            if cnt_before < total {
                let idx = fenwick_kth(&bit, m, cnt_before + 1);
                let diff = uniq[idx] - q;
                if diff < ans {
                    ans = diff;
                }
            }
        }

        j += 1;
    }

    ans
}

fn lower_bound(vals: &[i64], target: i64) -> usize {
    let mut lo = 0usize;
    let mut hi = vals.len();

    while lo < hi {
        let mid = (lo + hi) / 2;
        if vals[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo
}

fn fenwick_prefix(bit: &[i64], i: usize) -> i64 {
    let mut idx = i;
    let mut sum = 0i64;

    while idx > 0 {
        sum += bit[idx];
        let lb = idx & (idx ^ (idx - 1));
        idx -= lb;
    }

    sum
}

fn fenwick_kth(bit: &[i64], n: usize, k: i64) -> usize {
    let mut step = 1usize;
    while step * 2 <= n {
        step = step * 2;
    }

    let mut pos = 0usize;
    let mut target = k;

    while step > 0 {
        let next = pos + step;
        if next <= n && bit[next] < target {
            pos = next;
            target -= bit[next];
        }
        step = step / 2;
    }

    pos
}
