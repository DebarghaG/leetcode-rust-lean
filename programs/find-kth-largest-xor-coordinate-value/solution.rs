pub fn kth_largest_value(matrix: &[Vec<i64>], k: i64) -> i64 {
    let m = matrix.len();
    if m == 0 {
        return 0;
    }
    let n = matrix[0].len();

    let mut vals: Vec<i64> = Vec::new();
    let mut max_val: i64 = 0;
    let mut prev: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < m {
        let row = &matrix[i];
        let mut curr: Vec<i64> = Vec::new();
        let mut j: usize = 0;

        while j < n {
            let x = row[j];

            let mut left: i64 = 0;
            if j > 0 {
                left = curr[j - 1];
            }

            let mut up: i64 = 0;
            let mut diag: i64 = 0;
            if i > 0 {
                up = prev[j];
                if j > 0 {
                    diag = prev[j - 1];
                }
            }

            let val = x ^ up ^ left ^ diag;
            curr.push(val);
            vals.push(val);

            if val > max_val {
                max_val = val;
            }

            j += 1;
        }

        prev = curr;
        i += 1;
    }

    let count_len: usize = (max_val as usize) + 1;
    let mut counts: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < count_len {
        counts.push(0);
        z += 1;
    }

    let mut t: usize = 0;
    while t < vals.len() {
        let idx = vals[t] as usize;
        let c = counts[idx];
        counts[idx] = c + 1;
        t += 1;
    }

    let mut acc: i64 = 0;
    let mut idx: usize = count_len;
    while idx > 0 {
        idx = idx - 1;
        acc += counts[idx];
        if acc >= k {
            return idx as i64;
        }
    }

    0
}
