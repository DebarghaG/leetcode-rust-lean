pub fn create_sorted_array(instructions: &[i64]) -> i64 {
    let n = instructions.len();
    if n == 0 {
        return 0;
    }

    let mut vals: Vec<i64> = Vec::new();
    let mut idxs: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        vals.push(instructions[i]);
        idxs.push(i as i64);
        i += 1;
    }

    let mut temp_vals: Vec<i64> = Vec::new();
    let mut temp_idxs: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        temp_vals.push(0);
        temp_idxs.push(0);
        i += 1;
    }

    let mut less: Vec<i64> = Vec::new();
    let mut greater: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        less.push(0);
        greater.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let two_width = width * 2;
        let mut start: usize = 0;

        while start < n {
            let mid = if start + width < n { start + width } else { n };
            let end = if start + two_width < n { start + two_width } else { n };

            let mut l = start;
            let mut r = mid;
            let mut k = start;
            let mut first_ge = start;

            while l < mid && r < end {
                if vals[l] <= vals[r] {
                    temp_vals[k] = vals[l];
                    temp_idxs[k] = idxs[l];
                    l += 1;
                    k += 1;
                } else {
                    let x = vals[r];
                    while first_ge < mid && vals[first_ge] < x {
                        first_ge += 1;
                    }

                    let orig = idxs[r];
                    let o = orig as usize;
                    less[o] += (first_ge - start) as i64;
                    greater[o] += (mid - l) as i64;

                    temp_vals[k] = vals[r];
                    temp_idxs[k] = idxs[r];
                    r += 1;
                    k += 1;
                }
            }

            while l < mid {
                temp_vals[k] = vals[l];
                temp_idxs[k] = idxs[l];
                l += 1;
                k += 1;
            }

            while r < end {
                let x = vals[r];
                while first_ge < mid && vals[first_ge] < x {
                    first_ge += 1;
                }

                let orig = idxs[r];
                let o = orig as usize;
                less[o] += (first_ge - start) as i64;

                temp_vals[k] = vals[r];
                temp_idxs[k] = idxs[r];
                r += 1;
                k += 1;
            }

            start += two_width;
        }

        i = 0;
        while i < n {
            vals[i] = temp_vals[i];
            idxs[i] = temp_idxs[i];
            i += 1;
        }

        width = two_width;
    }

    let mod_val: i64 = 1000000007;
    let mut ans: i64 = 0;
    i = 0;
    while i < n {
        let cost = if less[i] < greater[i] {
            less[i]
        } else {
            greater[i]
        };
        ans = (ans + cost) % mod_val;
        i += 1;
    }

    ans
}
