pub fn max_sum(nums1: &[i64], nums2: &[i64]) -> i64 {
    let n1 = nums1.len();
    let n2 = nums2.len();

    let mut i: usize = 0;
    let mut j: usize = 0;

    let mut sum1: i64 = 0;
    let mut sum2: i64 = 0;
    let mut total: i64 = 0;

    while i < n1 && j < n2 {
        if nums1[i] < nums2[j] {
            sum1 = sum1 + nums1[i];
            i = i + 1;
        } else if nums1[i] > nums2[j] {
            sum2 = sum2 + nums2[j];
            j = j + 1;
        } else {
            if sum1 > sum2 {
                total = total + sum1;
            } else {
                total = total + sum2;
            }
            total = total + nums1[i];
            sum1 = 0;
            sum2 = 0;
            i = i + 1;
            j = j + 1;
        }
    }

    while i < n1 {
        sum1 = sum1 + nums1[i];
        i = i + 1;
    }

    while j < n2 {
        sum2 = sum2 + nums2[j];
        j = j + 1;
    }

    if sum1 > sum2 {
        total = total + sum1;
    } else {
        total = total + sum2;
    }

    total % 1000000007
}
