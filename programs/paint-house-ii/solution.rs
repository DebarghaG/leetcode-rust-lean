pub fn min_cost_ii(costs: &[Vec<i64>]) -> i64 {
    let n = costs.len();
    if n == 0 {
        return 0;
    }
    let k = costs[0].len();
    if k == 0 {
        return 0;
    }

    let mut prev: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < k {
        prev.push(costs[0][j]);
        j += 1;
    }

    let inf: i64 = 1000000000;
    let mut i: usize = 1;
    while i < n {
        let row = &costs[i];

        // First minimum value and its index.
        let mut min_val: i64 = prev[0];
        let mut min_idx: usize = 0;
        let mut c: usize = 1;
        while c < k {
            if prev[c] < min_val {
                min_val = prev[c];
                min_idx = c;
            }
            c += 1;
        }

        // Second minimum value (smallest among indices != min_idx).
        let mut min2: i64 = inf;
        let mut c2: usize = 0;
        while c2 < k {
            if c2 != min_idx {
                if prev[c2] < min2 {
                    min2 = prev[c2];
                }
            }
            c2 += 1;
        }

        // Build the next DP row.
        let mut curr: Vec<i64> = Vec::new();
        let mut col: usize = 0;
        while col < k {
            let mut add: i64 = min_val;
            if col == min_idx {
                add = min2;
            }
            curr.push(row[col] + add);
            col += 1;
        }

        prev = curr;
        i += 1;
    }

    let mut ans: i64 = prev[0];
    let mut c: usize = 1;
    while c < k {
        if prev[c] < ans {
            ans = prev[c];
        }
        c += 1;
    }
    ans
}
