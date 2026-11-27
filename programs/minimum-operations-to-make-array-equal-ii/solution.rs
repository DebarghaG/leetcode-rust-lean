pub fn min_operations(nums1: &[i64], nums2: &[i64], k: i64) -> i64 {
    let n = nums1.len();
    let mut result: i64 = 0;

    if k == 0 {
        let mut ok = true;
        let mut i = 0;
        while i < n {
            if nums1[i] != nums2[i] {
                ok = false;
            }
            i += 1;
        }
        if ok {
            result = 0;
        } else {
            result = -1;
        }
    } else {
        let mut positive: i64 = 0;
        let mut negative: i64 = 0;
        let mut feasible = true;
        let mut i = 0;
        while i < n {
            let diff = nums1[i] - nums2[i];
            if diff % k != 0 {
                feasible = false;
            } else {
                if diff > 0 {
                    positive += diff / k;
                } else if diff < 0 {
                    negative += (nums2[i] - nums1[i]) / k;
                }
            }
            i += 1;
        }
        if feasible && positive == negative {
            result = positive;
        } else {
            result = -1;
        }
    }

    result
}
