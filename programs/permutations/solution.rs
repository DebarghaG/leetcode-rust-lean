pub fn permute(nums: &[i64]) -> Vec<Vec<i64>> {
    let n = nums.len();
    let mut out: Vec<Vec<i64>> = Vec::new();

    if n == 0 {
        let mut empty_row: Vec<i64> = Vec::new();
        out.push(empty_row);
        return out;
    }

    // perm stores a permutation of indices 0..n-1 as i64 values.
    let mut perm: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    let mut val: i64 = 0;
    while idx < n {
        perm.push(val);
        idx += 1;
        val += 1;
    }

    let mut done = false;
    while !done {
        // Build the current output row by mapping each index in perm to nums.
        let mut row: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < n {
            let target: i64 = perm[k];
            let mut j: usize = 0;
            let mut jval: i64 = 0;
            let mut found_val: i64 = 0;
            while j < n {
                if jval == target {
                    found_val = nums[j];
                }
                j += 1;
                jval += 1;
            }
            row.push(found_val);
            k += 1;
        }
        out.push(row);

        // Compute the next lexicographic permutation of perm.
        if n <= 1 {
            done = true;
        } else {
            let mut pivot: usize = n;
            let mut found_pivot = false;
            let mut kk: usize = n;

            while kk > 0 && !found_pivot {
                if kk >= 2 {
                    let a: usize = kk - 2;
                    let b: usize = kk - 1;
                    if perm[a] < perm[b] {
                        pivot = a;
                        found_pivot = true;
                    }
                }
                if !found_pivot {
                    kk -= 1;
                }
            }

            if !found_pivot {
                done = true;
            } else {
                let mut jj: usize = n - 1;
                while jj > pivot && perm[pivot] >= perm[jj] {
                    jj -= 1;
                }

                let mut next: Vec<i64> = Vec::new();

                let mut p: usize = 0;
                while p < pivot {
                    next.push(perm[p]);
                    p += 1;
                }
                next.push(perm[jj]);

                let mut p2: usize = n;
                while p2 > pivot + 1 {
                    let idx2: usize = p2 - 1;
                    if idx2 == jj {
                        next.push(perm[pivot]);
                    } else {
                        next.push(perm[idx2]);
                    }
                    p2 -= 1;
                }

                perm = next;
            }
        }
    }

    out
}
