pub fn min_sum(nums1: &[i64], nums2: &[i64]) -> i64 {
    let mut sum1: i64 = 0;
    let mut zeros1: i64 = 0;
    let mut i: usize = 0;
    while i < nums1.len() {
        sum1 += nums1[i];
        if nums1[i] == 0 {
            zeros1 += 1;
        }
        i += 1;
    }

    let mut sum2: i64 = 0;
    let mut zeros2: i64 = 0;
    let mut j: usize = 0;
    while j < nums2.len() {
        sum2 += nums2[j];
        if nums2[j] == 0 {
            zeros2 += 1;
        }
        j += 1;
    }

    let min1: i64 = sum1 + zeros1;
    let min2: i64 = sum2 + zeros2;

    if zeros1 == 0 && zeros2 == 0 {
        if sum1 == sum2 {
            return sum1;
        } else {
            return -1;
        }
    }

    if zeros1 == 0 {
        if min2 <= sum1 {
            return sum1;
        } else {
            return -1;
        }
    }

    if zeros2 == 0 {
        if min1 <= sum2 {
            return sum2;
        } else {
            return -1;
        }
    }

    if min1 > min2 {
        min1
    } else {
        min2
    }
}
