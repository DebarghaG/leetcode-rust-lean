pub fn min_zero_array(nums: &[i64], queries: &[Vec<i64>]) -> i64 {
    let q = queries.len();

    if !feasible(nums, queries, q) {
        return -1;
    }

    let mut lo: usize = 0;
    let mut hi: usize = q;

    while lo < hi {
        let mid: usize = lo + (hi - lo) / 2;
        if feasible(nums, queries, mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo as i64
}

fn feasible(nums: &[i64], queries: &[Vec<i64>], k: usize) -> bool {
    let n = nums.len();

    let mut diff: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= n {
        diff.push(0);
        i += 1;
    }

    let mut j: usize = 0;
    while j < k {
        let row = &queries[j];
        let l = row[0] as usize;
        let r = row[1] as usize;
        let v = row[2];

        diff[l] += v;
        if r + 1 < n {
            diff[r + 1] -= v;
        }

        j += 1;
    }

    let mut cur: i64 = 0;
    let mut idx: usize = 0;

    while idx < n {
        cur += diff[idx];
        if cur < nums[idx] {
            return false;
        }
        idx += 1;
    }

    true
}
