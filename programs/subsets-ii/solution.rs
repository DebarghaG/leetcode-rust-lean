pub fn subsets_with_dup(nums: &[i64]) -> Vec<Vec<i64>> {
    let n = nums.len();

    let mut a: Vec<i64> = Vec::new();
    let mut i0 = 0;
    while i0 < n {
        a.push(nums[i0]);
        i0 += 1;
    }

    // Insertion sort.
    let mut i = 1;
    while i < a.len() {
        let key = a[i];
        let mut j = i;
        while j > 0 && a[j - 1] > key {
            a[j] = a[j - 1];
            j -= 1;
        }
        a[j] = key;
        i += 1;
    }

    let mut values: Vec<i64> = Vec::new();
    let mut max_counts: Vec<i64> = Vec::new();

    let mut p = 0;
    while p < a.len() {
        let v = a[p];
        let mut c: i64 = 0;
        while p < a.len() && a[p] == v {
            c += 1;
            p += 1;
        }
        values.push(v);
        max_counts.push(c);
    }

    let m = values.len();

    let mut choice: Vec<i64> = Vec::new();
    let mut q = 0;
    while q < m {
        choice.push(max_counts[q]);
        q += 1;
    }

    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut done = false;

    while !done {
        let mut subset: Vec<i64> = Vec::new();

        let mut g = 0;
        while g < m {
            let mut k: i64 = 0;
            while k < choice[g] {
                subset.push(values[g]);
                k += 1;
            }
            g += 1;
        }

        out.push(subset);

        let mut found = false;
        let mut r = m;

        while r > 0 && !found {
            let idx = r - 1;
            if choice[idx] > 0 {
                choice[idx] = choice[idx] - 1;

                let mut s = idx + 1;
                while s < m {
                    choice[s] = max_counts[s];
                    s += 1;
                }

                found = true;
            } else {
                r -= 1;
            }
        }

        if !found {
            done = true;
        }
    }

    out
}
