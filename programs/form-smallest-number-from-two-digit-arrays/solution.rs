pub fn min_number(nums1: &[i64], nums2: &[i64]) -> i64 {
    let mut common: i64 = 10;

    let mut i: usize = 0;
    while i < nums1.len() {
        let mut j: usize = 0;
        while j < nums2.len() {
            if nums1[i] == nums2[j] {
                if nums1[i] < common {
                    common = nums1[i];
                }
            }
            j += 1;
        }
        i += 1;
    }

    if common < 10 {
        return common;
    }

    let mut min1: i64 = 10;
    let mut i2: usize = 0;
    while i2 < nums1.len() {
        if nums1[i2] < min1 {
            min1 = nums1[i2];
        }
        i2 += 1;
    }

    let mut min2: i64 = 10;
    let mut j2: usize = 0;
    while j2 < nums2.len() {
        if nums2[j2] < min2 {
            min2 = nums2[j2];
        }
        j2 += 1;
    }

    let mut lo: i64 = min1;
    let mut hi: i64 = min2;
    if min2 < min1 {
        lo = min2;
        hi = min1;
    }

    lo * 10 + hi
}
