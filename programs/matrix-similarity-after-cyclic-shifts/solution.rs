pub fn are_similar(mat: &[Vec<i64>], k: i64) -> bool {
    let m = mat.len();
    let mut similar: bool = true;
    let mut i: usize = 0;

    while i < m {
        if similar {
            let row = &mat[i];
            let n = row.len();

            // Compute shift = k mod n using a simple loop (no nested returns).
            let mut shift: usize = 0;
            let mut step: i64 = 0;
            while step < k {
                shift += 1;
                if shift == n {
                    shift = 0;
                }
                step += 1;
            }

            // Even rows shift left by `shift`; odd rows shift right, i.e. left by n - shift.
            let mut delta: usize = 0;
            if i % 2 == 0 {
                delta = shift;
            } else {
                if shift == 0 {
                    delta = 0;
                } else {
                    delta = n - shift;
                }
            }

            let mut j: usize = 0;
            while j < n {
                let mut idx = j + delta;
                if idx >= n {
                    idx -= n;
                }
                if row[j] != row[idx] {
                    similar = false;
                }
                j += 1;
            }
        }
        i += 1;
    }

    similar
}
