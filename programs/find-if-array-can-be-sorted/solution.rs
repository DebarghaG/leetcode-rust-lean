fn popcount(mut x: i64) -> i64 {
    let mut count = 0;
    while x > 0 {
        if x % 2 == 1 {
            count += 1;
        }
        x = x / 2;
    }
    count
}

pub fn can_sort_array(nums: &[i64]) -> bool {
    let n = nums.len();

    // Copy input into an owned mutable buffer.
    let mut a: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < n {
        a.push(nums[t]);
        t += 1;
    }

    // For each maximal contiguous run of equal popcount, sort it.
    let mut i: usize = 0;
    while i < n {
        let bits = popcount(a[i]);

        // Find the end of the run [i, j).
        let mut j: usize = i;
        let mut scanning = true;
        while j < n && scanning {
            if popcount(a[j]) == bits {
                j += 1;
            } else {
                scanning = false;
            }
        }

        // Insertion sort on a[i..j].
        let mut p: usize = i + 1;
        while p < j {
            let key = a[p];
            let mut q: usize = p;
            let mut placing = true;
            while q > i && placing {
                if a[q - 1] > key {
                    a[q] = a[q - 1];
                    q -= 1;
                } else {
                    placing = false;
                }
            }
            a[q] = key;
            p += 1;
        }

        i = j;
    }

    // Verify the fully processed array is in ascending order.
    let mut ok = true;
    let mut k: usize = 1;
    while k < n {
        if a[k - 1] > a[k] {
            ok = false;
        }
        k += 1;
    }
    ok
}
