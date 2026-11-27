pub fn maximum_matching_indices(nums1: &[i64], nums2: &[i64]) -> i64 {
    let n = nums1.len();
    if n == 0 {
        return 0;
    }

    let mut best: i64 = 0;
    let mut shift: usize = 0;

    while shift < n {
        let mut current: i64 = 0;
        let mut i: usize = 0;

        while i < n {
            let mut j = i + shift;
            if j >= n {
                j -= n;
            }

            if nums1[i] == nums2[j] {
                current += 1;
            }

            i += 1;
        }

        if current > best {
            best = current;
        }

        shift += 1;
    }

    best
}
