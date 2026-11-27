pub fn added_integer(nums1: &[i64], nums2: &[i64]) -> i64 {
    let mut min1: i64 = nums1[0];
    let mut min2: i64 = nums2[0];

    let mut i: usize = 1;
    while i < nums1.len() {
        if nums1[i] < min1 {
            min1 = nums1[i];
        }
        i += 1;
    }

    i = 1;
    while i < nums2.len() {
        if nums2[i] < min2 {
            min2 = nums2[i];
        }
        i += 1;
    }

    min2 - min1
}
