pub fn max_total_fruits(fruits: &[Vec<i64>], startPos: i64, k: i64) -> i64 {
    let n = fruits.len();
    if n == 0 {
        return 0;
    }

    // Extract positions and amounts.
    let mut pos: Vec<i64> = Vec::new();
    let mut amt: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        pos.push(fruits[i][0]);
        amt.push(fruits[i][1]);
        i = i + 1;
    }

    // Prefix sums of amounts: prefix[j] = sum of amt[0..j].
    let mut prefix: Vec<i64> = Vec::new();
    prefix.push(0);
    let mut i: usize = 0;
    while i < n {
        let s = prefix[i] + amt[i];
        prefix.push(s);
        i = i + 1;
    }

    let mut best: i64 = 0;
    let mut l: usize = 0;
    let mut r: usize = 0;

    while r < n {
        // Advance l until the window [l, r] is reachable within k steps.
        let mut done = false;
        while !done {
            if l > r {
                done = true;
            } else {
                let pl = pos[l];
                let pr = pos[r];
                let left = if startPos > pl { startPos - pl } else { 0 };
                let right = if pr > startPos { pr - startPos } else { 0 };
                let c1 = 2 * left + right;
                let c2 = left + 2 * right;
                let cost = if c1 < c2 { c1 } else { c2 };
                if cost > k {
                    l = l + 1;
                } else {
                    done = true;
                }
            }
        }

        if l <= r {
            let sum = prefix[r + 1] - prefix[l];
            if sum > best {
                best = sum;
            }
        }

        r = r + 1;
    }

    best
}
