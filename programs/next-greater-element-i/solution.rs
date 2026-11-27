pub fn next_greater_element(nums1: &[i64], nums2: &[i64]) -> Vec<i64> {
    let mut ans: Vec<i64> = Vec::new();
    let n1 = nums1.len();
    let n2 = nums2.len();

    let mut i = 0;
    while i < n1 {
        let target = nums1[i];

        let mut pos = 0;
        let mut found = false;
        while pos < n2 && !found {
            if nums2[pos] == target {
                found = true;
            } else {
                pos += 1;
            }
        }

        let mut value: i64 = -1;
        if found {
            let mut j = pos + 1;
            let mut done = false;
            while j < n2 && !done {
                if nums2[j] > target {
                    value = nums2[j];
                    done = true;
                } else {
                    j += 1;
                }
            }
        }

        ans.push(value);
        i += 1;
    }

    ans
}
