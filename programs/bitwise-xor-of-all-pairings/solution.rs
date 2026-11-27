pub fn xor_all_nums(nums1: &[i64], nums2: &[i64]) -> i64 {
    let mut xor1: i64 = 0;
    let mut xor2: i64 = 0;

    let mut i: usize = 0;
    while i < nums1.len() {
        xor1 = xor1 ^ nums1[i];
        i += 1;
    }

    let mut j: usize = 0;
    while j < nums2.len() {
        xor2 = xor2 ^ nums2[j];
        j += 1;
    }

    let mut ans: i64 = 0;

    if nums2.len() % 2 == 1 {
        ans = ans ^ xor1;
    }

    if nums1.len() % 2 == 1 {
        ans = ans ^ xor2;
    }

    ans
}
