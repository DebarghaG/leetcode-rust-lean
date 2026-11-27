pub fn min_operations(initial: &[u8], target: &[u8]) -> i64 {
    let n: usize = initial.len();
    let m: usize = target.len();

    let mut prev: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < m + 1 {
        prev.push(0);
        z += 1;
    }

    let mut best: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let mut curr: Vec<i64> = Vec::new();
        let mut zz: usize = 0;
        while zz < m + 1 {
            curr.push(0);
            zz += 1;
        }

        let mut j: usize = 0;
        while j < m {
            if initial[i] == target[j] {
                let val: i64 = prev[j] + 1;
                curr[j + 1] = val;
                if val > best {
                    best = val;
                }
            }
            j += 1;
        }

        prev = curr;
        i += 1;
    }

    (n as i64) + (m as i64) - 2 * best
}
