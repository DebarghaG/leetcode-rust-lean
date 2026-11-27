fn fenwick_add(bit: &mut Vec<i64>, idx: usize, delta: i64) {
    let m = bit.len() - 1;
    let mut i = idx + 1;
    while i <= m {
        bit[i] = bit[i] + delta;
        let low = i & (i ^ (i - 1));
        i += low;
    }
}

fn value_rank(vals: &[i64], x: i64) -> usize {
    let mut lo = 0usize;
    let mut hi = vals.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if vals[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

fn sum_smallest(cnt: &[i64], fsum: &[i64], uniq: &[i64], t: i64) -> i64 {
    if t <= 0 {
        return 0;
    }

    let m = uniq.len();
    let mut step = 1usize;
    while step * 2 <= m {
        step *= 2;
    }

    let mut idx = 0usize;
    let mut acc_count: i64 = 0;
    let mut acc_sum: i64 = 0;

    while step > 0 {
        let next = idx + step;
        if next <= m {
            let c = cnt[next];
            if acc_count + c < t {
                idx = next;
                acc_count += c;
                acc_sum += fsum[next];
            }
        }
        step /= 2;
    }

    if idx >= m {
        return acc_sum;
    }

    let remaining = t - acc_count;
    let val = uniq[idx];
    acc_sum + remaining * val
}

pub fn minimum_cost(nums: &[i64], k: i64, dist: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }
    if k <= 1 {
        return nums[0];
    }

    let kk = k as usize;

    if kk == 2 {
        let mut best = nums[1];
        let mut i = 2usize;
        while i < n {
            if nums[i] < best {
                best = nums[i];
            }
            i += 1;
        }
        return nums[0] + best;
    }

    let dd = dist as usize;

    let mut sorted: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        sorted.push(nums[i]);
        i += 1;
    }
    sorted.sort();

    let mut uniq: Vec<i64> = Vec::new();
    let mut j = 0usize;
    while j < sorted.len() {
        let v = sorted[j];
        uniq.push(v);
        j += 1;
        while j < sorted.len() && sorted[j] == v {
            j += 1;
        }
    }

    let size = uniq.len();
    let mut cnt: Vec<i64> = Vec::new();
    let mut fsum: Vec<i64> = Vec::new();
    let mut z = 0usize;
    while z <= size {
        cnt.push(0);
        fsum.push(0);
        z += 1;
    }

    // Window for l = 1: other chosen starts may be in [2, min(n - 1, 1 + dist)].
    let right1 = if 1 + dd < n { 1 + dd } else { n - 1 };
    let mut p = 2usize;
    while p <= right1 {
        let v = nums[p];
        let r = value_rank(&uniq, v);
        fenwick_add(&mut cnt, r, 1);
        fenwick_add(&mut fsum, r, v);
        p += 1;
    }

    let t = (kk - 2) as i64;
    let last_l = n - kk + 1;
    let mut ans: i64 = 1_000_000_000_000_000_000;
    let mut l = 1usize;

    while l <= last_l {
        let small_sum = sum_smallest(&cnt, &fsum, &uniq, t);
        let cost = nums[0] + nums[l] + small_sum;
        if cost < ans {
            ans = cost;
        }

        if l < last_l {
            let rem_idx = l + 1;
            let rem_val = nums[rem_idx];
            let rem_rank = value_rank(&uniq, rem_val);
            fenwick_add(&mut cnt, rem_rank, -1);
            fenwick_add(&mut fsum, rem_rank, -rem_val);

            let add_idx = l + dd + 1;
            if add_idx < n {
                let add_val = nums[add_idx];
                let add_rank = value_rank(&uniq, add_val);
                fenwick_add(&mut cnt, add_rank, 1);
                fenwick_add(&mut fsum, add_rank, add_val);
            }
        }

        l += 1;
    }

    ans
}
