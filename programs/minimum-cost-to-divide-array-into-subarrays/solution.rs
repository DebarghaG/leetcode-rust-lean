pub fn minimum_cost(nums: &[i64], cost: &[i64], k: i64) -> i64 {
    let n: usize = nums.len();
    let inf: i64 = 4_000_000_000_000_000_000;

    let mut pref_nums: Vec<i64> = Vec::new();
    let mut pref_cost: Vec<i64> = Vec::new();
    pref_nums.push(0);
    pref_cost.push(0);

    let mut i: usize = 0;
    while i < n {
        let last_nums = pref_nums[i];
        pref_nums.push(last_nums + nums[i]);
        let last_cost = pref_cost[i];
        pref_cost.push(last_cost + cost[i]);
        i += 1;
    }

    // dp_prev[j] = min cost to divide first j elements into (parts-1) subarrays.
    let mut dp_prev: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t <= n {
        if t == 0 {
            dp_prev.push(0);
        } else {
            dp_prev.push(inf);
        }
        t += 1;
    }

    let mut ans: i64 = inf;
    let mut parts: usize = 1;
    let mut parts_i: i64 = 1;

    while parts <= n {
        // Build dp_cur element by element with push only.
        let mut dp_cur: Vec<i64> = Vec::new();

        // Indices 0..parts-1 are unreachable with `parts` subarrays.
        let mut z: usize = 0;
        while z < parts {
            dp_cur.push(inf);
            z += 1;
        }

        // Lower convex hull of lines y = m*x + b (dynamic deque via two stacks + head index).
        let mut ms: Vec<i64> = Vec::new();
        let mut bs: Vec<i64> = Vec::new();
        let mut head: usize = 0;

        let mut r: usize = parts;
        while r <= n {
            let l: usize = r - 1;
            let b: i64 = dp_prev[l];

            if b < inf {
                let m: i64 = -pref_cost[l];

                while ms.len() >= head + 2 {
                    let m1 = ms[ms.len() - 2];
                    let b1 = bs[bs.len() - 2];
                    let m2 = ms[ms.len() - 1];
                    let b2 = bs[bs.len() - 1];

                    if (b2 - b1) * (m2 - m) >= (b - b2) * (m1 - m2) {
                        ms.pop();
                        bs.pop();
                    } else {
                        break;
                    }
                }

                ms.push(m);
                bs.push(b);
            }

            let x: i64 = pref_nums[r] + k * parts_i;

            while head + 1 < ms.len() {
                let v0 = ms[head] * x + bs[head];
                let v1 = ms[head + 1] * x + bs[head + 1];
                if v1 <= v0 {
                    head += 1;
                } else {
                    break;
                }
            }

            let best = ms[head] * x + bs[head];
            dp_cur.push(x * pref_cost[r] + best);

            r += 1;
        }

        let cand = dp_cur[n];
        if cand < ans {
            ans = cand;
        }

        dp_prev = dp_cur;
        parts += 1;
        parts_i += 1;
    }

    ans
}
