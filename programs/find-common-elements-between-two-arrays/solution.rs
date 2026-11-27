pub fn find_intersection_values(nums1: &[i64], nums2: &[i64]) -> Vec<i64> {
    let n = nums1.len();
    let m = nums2.len();

    let mut answer1: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let mut found: bool = false;
        let mut j: usize = 0;
        while j < m {
            if nums1[i] == nums2[j] {
                found = true;
            }
            j += 1;
        }
        if found {
            answer1 += 1;
        }
        i += 1;
    }

    let mut answer2: i64 = 0;
    let mut i2: usize = 0;
    while i2 < m {
        let mut found: bool = false;
        let mut j2: usize = 0;
        while j2 < n {
            if nums2[i2] == nums1[j2] {
                found = true;
            }
            j2 += 1;
        }
        if found {
            answer2 += 1;
        }
        i2 += 1;
    }

    let mut result: Vec<i64> = Vec::new();
    result.push(answer1);
    result.push(answer2);
    result
}
