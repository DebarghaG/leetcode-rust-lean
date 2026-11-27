pub fn beautiful_pair(nums1: &[i64], nums2: &[i64]) -> Vec<i64> {
    let n = nums1.len();

    let mut best_d: i64 = abs_diff(nums1[0], nums1[1]) + abs_diff(nums2[0], nums2[1]);
    let mut best_i: i64 = 0;
    let mut best_j: i64 = 1;

    let mut i = 0;
    while i < n {
        let mut j = i + 1;
        while j < n {
            let d = abs_diff(nums1[i], nums1[j]) + abs_diff(nums2[i], nums2[j]);
            // Pairs are visited in lexicographic order (i asc, then j asc),
            // so strict `<` keeps the first (lexicographically smallest) pair.
            if d < best_d {
                best_d = d;
                best_i = i as i64;
                best_j = j as i64;
            }
            j += 1;
        }
        i += 1;
    }

    let mut out: Vec<i64> = Vec::new();
    out.push(best_i);
    out.push(best_j);
    out
}

fn abs_diff(a: i64, b: i64) -> i64 {
    if a >= b { a - b } else { b - a }
}
