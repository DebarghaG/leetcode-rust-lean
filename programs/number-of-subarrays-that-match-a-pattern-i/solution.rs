pub fn count_matching_subarrays(nums: &[i64], pattern: &[i64]) -> i64 {
    let n = nums.len();
    let m = pattern.len();
    if m + 1 > n {
        return 0;
    }

    let total = n - m; // number of valid starting positions
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < total {
        let mut ok: bool = true;
        let mut k: usize = 0;
        while k < m {
            let a = nums[i + k];
            let b = nums[i + k + 1];
            let p = pattern[k];
            if p == 1 {
                if !(b > a) {
                    ok = false;
                }
            } else if p == 0 {
                if !(b == a) {
                    ok = false;
                }
            } else {
                if !(b < a) {
                    ok = false;
                }
            }
            if !ok {
                break;
            }
            k += 1;
        }
        if ok {
            count += 1;
        }
        i += 1;
    }

    count
}
