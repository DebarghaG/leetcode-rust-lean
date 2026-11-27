pub fn count_of_pairs(n: i64, x: i64, y: i64) -> Vec<i64> {
    let mut ans: Vec<i64> = Vec::new();
    let mut i: i64 = 0;
    while i < n {
        ans.push(0);
        i += 1;
    }

    // If x == y, the extra street does not change the graph:
    // it is just a path 1 - 2 - ... - n.
    if x == y {
        let mut k: i64 = 1;
        while k <= n {
            ans[(k - 1) as usize] = 2 * (n - k);
            k += 1;
        }
        return ans;
    }

    let mut a = x;
    let mut b = y;
    if a > b {
        let tmp = a;
        a = b;
        b = tmp;
    }

    let left = a - 1;              // vertices strictly left of a
    let cycle_len = b - a + 1;     // vertices a, a+1, ..., b forming a cycle
    let right = n - b;             // vertices strictly right of b
    let half = cycle_len / 2;

    let mut diff: Vec<i64> = Vec::new();
    i = 0;
    while i < n + 3 {
        diff.push(0);
        i += 1;
    }

    // Pairs fully inside the left tail or fully inside the right tail.
    let mut d: i64 = 1;
    while d < left {
        let val = left - d;
        diff[d as usize] += val;
        diff[(d + 1) as usize] -= val;
        d += 1;
    }

    d = 1;
    while d < right {
        let val = right - d;
        diff[d as usize] += val;
        diff[(d + 1) as usize] -= val;
        d += 1;
    }

    // Pairs where both vertices are on the cycle.
    d = 1;
    while d <= half {
        let mult: i64;
        if cycle_len % 2 == 0 && d == half {
            mult = cycle_len / 2;
        } else {
            mult = cycle_len;
        }
        diff[d as usize] += mult;
        diff[(d + 1) as usize] -= mult;
        d += 1;
    }

    // Pairs with one vertex on a tail and one vertex on the cycle.
    // For a fixed cycle vertex, the number of cycle vertices at distance d
    // from the attachment point is: 1 for d = 0, 2 normally, and possibly
    // 1 at the far half when the cycle length is even.
    d = 0;
    while d <= half {
        let mut mult: i64 = 2;
        if d == 0 {
            mult = 1;
        } else if cycle_len % 2 == 0 && d == half {
            mult = 1;
        }

        if left > 0 {
            let lo = d + 1;
            let hi = d + left;
            diff[lo as usize] += mult;
            diff[(hi + 1) as usize] -= mult;
        }

        if right > 0 {
            let lo = d + 1;
            let hi = d + right;
            diff[lo as usize] += mult;
            diff[(hi + 1) as usize] -= mult;
        }

        d += 1;
    }

    // Pairs with one vertex in the left tail and one vertex in the right tail.
    // Distance = t + s + 1, where t and s are tail distances from a and b.
    if left > 0 && right > 0 {
        let mut t: i64 = 1;
        while t <= left {
            let lo = t + 2;
            let hi = t + right + 1;
            diff[lo as usize] += 1;
            diff[(hi + 1) as usize] -= 1;
            t += 1;
        }
    }

    // Prefix sums turn range additions into exact counts.
    // Counts are currently unordered pairs; multiply by 2 for ordered pairs.
    let mut cur: i64 = 0;
    let mut k: i64 = 1;
    while k <= n {
        cur += diff[k as usize];
        ans[(k - 1) as usize] = 2 * cur;
        k += 1;
    }

    ans
}
