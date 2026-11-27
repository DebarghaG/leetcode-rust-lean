fn lower_bound(xs: &Vec<i64>, target: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = xs.len();

    while lo < hi {
        let mid: usize = lo + (hi - lo) / 2;
        if xs[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo
}

pub fn count_interesting_subarrays(nums: &[i64], modulo: i64, k: i64) -> i64 {
    let n: usize = nums.len();

    let mut prefix: Vec<i64> = Vec::new();
    let mut cur: i64 = 0;
    prefix.push(0);

    let mut i: usize = 0;
    while i < n {
        if nums[i] % modulo == k {
            cur = cur + 1;
            if cur >= modulo {
                cur = cur % modulo;
            }
        }
        prefix.push(cur);
        i += 1;
    }

    let mut sorted: Vec<i64> = Vec::new();
    let mut i2: usize = 0;
    while i2 < prefix.len() {
        sorted.push(prefix[i2]);
        i2 += 1;
    }

    sorted.sort();

    let mut unique: Vec<i64> = Vec::new();
    let mut i3: usize = 0;
    while i3 < sorted.len() {
        if i3 == 0 || sorted[i3] != sorted[i3 - 1] {
            unique.push(sorted[i3]);
        }
        i3 += 1;
    }

    let m: usize = unique.len();
    let mut freq: Vec<i64> = Vec::new();
    let mut i4: usize = 0;
    while i4 < m {
        freq.push(0);
        i4 += 1;
    }

    let mut ans: i64 = 0;
    let mut p: usize = 0;
    while p < prefix.len() {
        let val: i64 = prefix[p];

        let target: i64 = if val >= k {
            val - k
        } else {
            val + modulo - k
        };

        let idx: usize = lower_bound(&unique, target);
        if idx < m && unique[idx] == target {
            ans += freq[idx];
        }

        let idx_cur: usize = lower_bound(&unique, val);
        freq[idx_cur] += 1;

        p += 1;
    }

    ans
}
