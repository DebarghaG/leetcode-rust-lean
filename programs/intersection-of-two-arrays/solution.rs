pub fn intersection(nums1: &[i64], nums2: &[i64]) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();
    let n1 = nums1.len();
    let n2 = nums2.len();

    let mut i: usize = 0;
    while i < n2 {
        let x = nums2[i];

        let mut in1 = false;
        let mut j: usize = 0;
        while j < n1 {
            if nums1[j] == x {
                in1 = true;
            }
            j += 1;
        }

        if in1 {
            let mut already_added = false;
            let mut k: usize = 0;
            while k < result.len() {
                if result[k] == x {
                    already_added = true;
                }
                k += 1;
            }

            if !already_added {
                result.push(x);
            }
        }

        i += 1;
    }

    result
}
