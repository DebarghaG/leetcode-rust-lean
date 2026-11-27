pub fn number_of_pairs(nums1: &[i64], nums2: &[i64], k: i64) -> i64 {
    let mut count: i64 = 0;
    let n = nums1.len();
    let m = nums2.len();

    let mut i: usize = 0;
    while i < n {
        let mut j: usize = 0;
        while j < m {
            let divisor = nums2[j] * k;
            if divisor != 0 && nums1[i] % divisor == 0 {
                count += 1;
            }
            j += 1;
        }
        i += 1;
    }

    count
}
