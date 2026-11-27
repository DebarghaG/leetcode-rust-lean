pub fn find_kth_largest(nums: &[i64], k: i64) -> i64 {
    let n: usize = nums.len();
    if n == 0 {
        return 0;
    }

    let mut v: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < n {
        v.push(nums[idx]);
        idx += 1;
    }

    let target: usize = n - (k as usize);
    let mut lo: usize = 0;
    let mut hi: usize = n - 1;

    while lo < hi {
        let mid: usize = lo + (hi - lo) / 2;
        let a: i64 = v[lo];
        let b: i64 = v[mid];
        let c: i64 = v[hi];

        let mut pivot: i64 = c;
        if (a <= b && b <= c) || (c <= b && b <= a) {
            pivot = b;
        } else if (b <= a && a <= c) || (c <= a && a <= b) {
            pivot = a;
        }

        let mut lt: usize = lo;
        let mut i: usize = lo;
        let mut gt: usize = hi + 1;

        while i < gt {
            if v[i] < pivot {
                let tmp: i64 = v[lt];
                v[lt] = v[i];
                v[i] = tmp;
                lt += 1;
                i += 1;
            } else if v[i] > pivot {
                gt -= 1;
                let tmp: i64 = v[i];
                v[i] = v[gt];
                v[gt] = tmp;
            } else {
                i += 1;
            }
        }

        if target < lt {
            hi = lt - 1;
        } else if target < gt {
            return v[lt];
        } else {
            lo = gt;
        }
    }

    v[lo]
}
