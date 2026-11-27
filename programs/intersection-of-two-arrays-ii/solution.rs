pub fn intersect(nums1: &[i64], nums2: &[i64]) -> Vec<i64> {
    let n2 = nums2.len();

    let mut used: Vec<bool> = Vec::new();
    let mut j = 0;
    while j < n2 {
        used.push(false);
        j += 1;
    }

    let mut out: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < nums1.len() {
        let mut j = 0;
        let mut found = false;

        while j < n2 && !found {
            if !used[j] && nums2[j] == nums1[i] {
                used[j] = true;
                out.push(nums1[i]);
                found = true;
            }
            j += 1;
        }

        i += 1;
    }

    // Sort the result in ascending order using insertion sort.
    let mut a = 1;
    while a < out.len() {
        let key = out[a];
        let mut b = a;

        while b > 0 && out[b - 1] > key {
            out[b] = out[b - 1];
            b -= 1;
        }

        out[b] = key;
        a += 1;
    }

    out
}
