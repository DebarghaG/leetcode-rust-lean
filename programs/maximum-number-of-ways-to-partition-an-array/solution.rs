fn hash_index(key: i64, mask: usize) -> usize {
    let mut h = key;
    if h < 0 {
        h = -h;
    }
    h = h * 1000003;
    h = h ^ (h >> 17);
    h = h ^ (h << 5);
    h = h ^ (h >> 13);
    (h as usize) & mask
}

fn find_slot(keys: &[i64], mask: usize, key: i64, empty: i64) -> usize {
    let mut idx = hash_index(key, mask);
    while keys[idx] != empty && keys[idx] != key {
        idx = (idx + 1) & mask;
    }
    idx
}

pub fn ways_to_partition(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n < 2 {
        return 0;
    }

    let mut sum_total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        sum_total += nums[i];
        i += 1;
    }

    let m: usize = n - 1;

    // diffs[p - 1] = 2 * prefix_sum(nums[0..p]) - sum_total
    // for pivot p, where 1 <= p <= n - 1.
    let mut diffs: Vec<i64> = Vec::new();
    let mut zero_count: i64 = 0;
    let mut prefix: i64 = 0;
    let mut p: usize = 1;
    while p < n {
        prefix += nums[p - 1];
        let d = 2 * prefix - sum_total;
        diffs.push(d);
        if d == 0 {
            zero_count += 1;
        }
        p += 1;
    }

    let empty: i64 = -1000000000000000000;

    // Power-of-two hash table size, with load factor below 1/2.
    let mut size: usize = 1;
    while size <= 2 * m {
        size = size * 2;
    }
    let mask: usize = size - 1;

    let mut keys: Vec<i64> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();
    i = 0;
    while i < size {
        keys.push(empty);
        counts.push(0);
        i += 1;
    }

    // First pass: left[i] = number of pivots p <= i with diffs[p-1] == k - nums[i].
    let mut left_counts: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        let delta = k - nums[i];
        let idx = find_slot(&keys, mask, delta, empty);

        let mut a: i64 = 0;
        if keys[idx] == delta {
            a = counts[idx];
        }
        left_counts.push(a);

        if i < m {
            let d = diffs[i];
            let idxd = find_slot(&keys, mask, d, empty);
            if keys[idxd] == empty {
                keys[idxd] = d;
                counts[idxd] = 1;
            } else {
                counts[idxd] += 1;
            }
        }

        i += 1;
    }

    // Reset the hash table for the right-side sweep.
    i = 0;
    while i < size {
        keys[i] = empty;
        counts[i] = 0;
        i += 1;
    }

    let mut ans: i64 = zero_count;

    // Second pass from right to left:
    // right[i] = number of pivots p > i with diffs[p-1] == -(k - nums[i]).
    i = n;
    while i > 0 {
        i -= 1;

        let delta = k - nums[i];
        let neg_delta = -delta;
        let idx = find_slot(&keys, mask, neg_delta, empty);

        let mut b: i64 = 0;
        if keys[idx] == neg_delta {
            b = counts[idx];
        }

        let ways = left_counts[i] + b;
        if ways > ans {
            ans = ways;
        }

        if i >= 1 {
            let d = diffs[i - 1];
            let idxd = find_slot(&keys, mask, d, empty);
            if keys[idxd] == empty {
                keys[idxd] = d;
                counts[idxd] = 1;
            } else {
                counts[idxd] += 1;
            }
        }
    }

    ans
}
