pub fn max_balanced_subsequence_sum(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut vals: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        vals.push(nums[i] - (i as i64));
        i += 1;
    }

    // Bottom-up merge sort on vals.
    let mut temp: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < n {
        temp.push(0);
        t += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut start: usize = 0;
        while start < n {
            let mut mid = start + width;
            if mid > n {
                mid = n;
            }

            let mut end = start + width * 2;
            if end > n {
                end = n;
            }

            let mut a = start;
            let mut b = mid;
            let mut k = start;

            while a < mid && b < end {
                if vals[a] <= vals[b] {
                    temp[k] = vals[a];
                    a += 1;
                } else {
                    temp[k] = vals[b];
                    b += 1;
                }
                k += 1;
            }

            while a < mid {
                temp[k] = vals[a];
                a += 1;
                k += 1;
            }

            while b < end {
                temp[k] = vals[b];
                b += 1;
                k += 1;
            }

            start = end;
        }

        let mut j: usize = 0;
        while j < n {
            vals[j] = temp[j];
            j += 1;
        }

        width = width * 2;
    }

    // Coordinate compression: build the unique sorted values.
    let mut uniq: Vec<i64> = Vec::new();
    let mut u: usize = 0;
    while u < n {
        if uniq.len() == 0 {
            uniq.push(vals[u]);
        } else {
            let last = uniq.len() - 1;
            if uniq[last] != vals[u] {
                uniq.push(vals[u]);
            }
        }
        u += 1;
    }

    let m = uniq.len();

    // Fenwick tree for prefix maximum queries.
    let mut tree: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z <= m {
        tree.push(0);
        z += 1;
    }

    let mut ans: i64 = nums[0];
    let mut i2: usize = 0;

    while i2 < n {
        let b = nums[i2] - (i2 as i64);

        // Lower bound: first index with uniq[index] >= b.
        let mut lo: usize = 0;
        let mut hi: usize = m;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if uniq[mid] < b {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        let pos = lo + 1;

        // Query maximum dp value among compressed indices <= pos.
        let mut best: i64 = 0;
        let mut p = pos;
        while p > 0 {
            if tree[p] > best {
                best = tree[p];
            }
            let low = p & (p ^ (p - 1));
            p -= low;
        }

        let cur = nums[i2] + best;
        if cur > ans {
            ans = cur;
        }

        // Only positive dp values can improve future answers.
        if cur > 0 {
            let mut p2 = pos;
            while p2 <= m {
                if tree[p2] < cur {
                    tree[p2] = cur;
                }
                let low2 = p2 & (p2 ^ (p2 - 1));
                p2 += low2;
            }
        }

        i2 += 1;
    }

    ans
}
