fn has_adjacent_increasing(inc: &[i64], n: usize, k: usize) -> bool {
    let mut a: usize = 0;
    let kk: i64 = k as i64;

    while a + 2 * k <= n {
        if inc[a] >= kk && inc[a + k] >= kk {
            return true;
        }
        a = a + 1;
    }

    false
}

pub fn max_increasing_subarrays(nums: &[i64]) -> i64 {
    let n = nums.len();

    if n < 2 {
        return 0;
    }

    let mut inc: Vec<i64> = Vec::new();
    let mut idx: usize = 0;

    while idx < n {
        inc.push(1);
        idx = idx + 1;
    }

    let mut i: usize = n;
    while i > 0 {
        i = i - 1;

        if i + 1 < n && nums[i] < nums[i + 1] {
            inc[i] = inc[i + 1] + 1;
        } else {
            inc[i] = 1;
        }
    }

    let mut lo: usize = 1;
    let mut hi: usize = n / 2;
    let mut ans: usize = 1;

    while lo <= hi {
        let mid: usize = lo + (hi - lo) / 2;

        if has_adjacent_increasing(&inc, n, mid) {
            ans = mid;
            lo = mid + 1;
        } else {
            hi = mid - 1;
        }
    }

    ans as i64
}
