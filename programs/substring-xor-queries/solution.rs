pub fn substring_xor_queries(s: &[u8], queries: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n = s.len();

    let mut child0: Vec<i64> = Vec::new();
    let mut child1: Vec<i64> = Vec::new();
    let mut earliest: Vec<i64> = Vec::new();

    child0.push(-1);
    child1.push(-1);
    earliest.push(-1);

    let mut first_zero: i64 = -1;
    let mut start: usize = 0;

    while start < n {
        if s[start] == b'0' {
            if first_zero == -1 {
                first_zero = start as i64;
            }
        } else {
            let mut node: i64 = 0;
            let mut j: usize = start;

            while j < n && j - start < 30 {
                if s[j] == b'1' {
                    let existing = child1[node as usize];
                    if existing == -1 {
                        let new_idx = child0.len() as i64;
                        child0.push(-1);
                        child1.push(-1);
                        earliest.push(start as i64);
                        child1[node as usize] = new_idx;
                        node = new_idx;
                    } else {
                        node = existing;
                    }
                } else {
                    let existing = child0[node as usize];
                    if existing == -1 {
                        let new_idx = child0.len() as i64;
                        child0.push(-1);
                        child1.push(-1);
                        earliest.push(start as i64);
                        child0[node as usize] = new_idx;
                        node = new_idx;
                    } else {
                        node = existing;
                    }
                }
                j += 1;
            }
        }
        start += 1;
    }

    let mut ans: Vec<Vec<i64>> = Vec::new();
    let mut qi: usize = 0;

    while qi < queries.len() {
        let first = queries[qi][0];
        let second = queries[qi][1];
        let target = first ^ second;

        let mut left: i64 = -1;
        let mut right: i64 = -1;

        if target == 0 {
            if first_zero != -1 {
                left = first_zero;
                right = first_zero;
            }
        } else {
            let mut len: i64 = 0;
            let mut tmp = target;
            while tmp > 0 {
                len += 1;
                tmp = tmp >> 1;
            }

            let mut node: i64 = 0;
            let mut k: i64 = len - 1;
            let mut missing: bool = false;

            while k >= 0 && !missing {
                let bit = (target >> k) & 1;
                let stored = if bit == 1 {
                    child1[node as usize]
                } else {
                    child0[node as usize]
                };

                if stored == -1 {
                    missing = true;
                } else {
                    node = stored;
                }

                k -= 1;
            }

            if !missing {
                let l = earliest[node as usize];
                left = l;
                right = l + len - 1;
            }
        }

        let mut row: Vec<i64> = Vec::new();
        row.push(left);
        row.push(right);
        ans.push(row);

        qi += 1;
    }

    ans
}
