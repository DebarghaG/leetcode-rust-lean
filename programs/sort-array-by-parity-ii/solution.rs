pub fn sort_array_by_parity_ii(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();

    // Copy into an owned vector so we can rearrange in place.
    let mut a: Vec<i64> = Vec::new();
    let mut k = 0;
    while k < n {
        a.push(nums[k]);
        k += 1;
    }

    // Two pointers: `i` looks for an even value at an odd position's counterpart,
    // `j` looks for an odd value at an even position's counterpart.
    let mut i: usize = 0; // expected even value slot
    let mut j: usize = 1; // expected odd value slot

    while i < n && j < n {
        while i < n && a[i] % 2 == 0 {
            i += 2;
        }
        while j < n && a[j] % 2 != 0 {
            j += 2;
        }
        if i < n && j < n {
            let tmp = a[i];
            a[i] = a[j];
            a[j] = tmp;
            i += 2;
            j += 2;
        }
    }

    a
}
