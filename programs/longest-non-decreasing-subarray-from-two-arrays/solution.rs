pub fn max_non_decreasing_length(nums1: &[i64], nums2: &[i64]) -> i64 {
    let n: usize = nums1.len();
    if n == 0 {
        return 0;
    }

    let mut dp1: i64 = 1;
    let mut dp2: i64 = 1;
    let mut ans: i64 = 1;

    let mut i: usize = 1;
    while i < n {
        let mut next1: i64 = 1;
        let mut next2: i64 = 1;

        if nums1[i] >= nums1[i - 1] {
            let cand: i64 = dp1 + 1;
            if cand > next1 {
                next1 = cand;
            }
        }
        if nums1[i] >= nums2[i - 1] {
            let cand: i64 = dp2 + 1;
            if cand > next1 {
                next1 = cand;
            }
        }

        if nums2[i] >= nums1[i - 1] {
            let cand: i64 = dp1 + 1;
            if cand > next2 {
                next2 = cand;
            }
        }
        if nums2[i] >= nums2[i - 1] {
            let cand: i64 = dp2 + 1;
            if cand > next2 {
                next2 = cand;
            }
        }

        dp1 = next1;
        dp2 = next2;

        if dp1 > ans {
            ans = dp1;
        }
        if dp2 > ans {
            ans = dp2;
        }

        i += 1;
    }

    ans
}
