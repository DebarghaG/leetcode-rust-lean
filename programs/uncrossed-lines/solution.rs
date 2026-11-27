pub fn max_uncrossed_lines(nums1: &[i64], nums2: &[i64]) -> i64 {
    let n: usize = nums1.len();
    let m: usize = nums2.len();

    let mut prev: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j <= m {
        prev.push(0);
        j += 1;
    }

    let mut i: usize = 1;
    while i <= n {
        let mut cur: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k <= m {
            cur.push(0);
            k += 1;
        }

        let mut j2: usize = 1;
        while j2 <= m {
            if nums1[i - 1] == nums2[j2 - 1] {
                cur[j2] = prev[j2 - 1] + 1;
            } else {
                let a: i64 = prev[j2];
                let b: i64 = cur[j2 - 1];
                if a >= b {
                    cur[j2] = a;
                } else {
                    cur[j2] = b;
                }
            }
            j2 += 1;
        }

        prev = cur;
        i += 1;
    }

    prev[m]
}
