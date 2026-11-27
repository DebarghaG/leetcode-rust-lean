pub fn max_subarrays(n: i64, conflictingPairs: &[Vec<i64>]) -> i64 {
    let m = conflictingPairs.len();
    let nn = n as usize;

    let mut groups: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i <= nn {
        groups.push(Vec::new());
        i += 1;
    }

    let mut pair_idx: usize = 0;
    while pair_idx < m {
        let p = &conflictingPairs[pair_idx];
        let mut a = p[0];
        let mut b = p[1];
        if a > b {
            let tmp = a;
            a = b;
            b = tmp;
        }
        groups[b as usize].push(pair_idx as i64);
        pair_idx += 1;
    }

    let mut gains: Vec<i64> = Vec::new();
    let mut gi: usize = 0;
    while gi < m {
        gains.push(0);
        gi += 1;
    }

    let mut max1: i64 = 0;
    let mut max2: i64 = 0;
    let mut cnt1: i64 = 0;
    let mut id1: i64 = -1;
    let mut baseline: i64 = 0;

    let mut r: i64 = 1;
    while r <= n {
        let ru = r as usize;
        let g = &groups[ru];
        let glen = g.len();

        let mut k: usize = 0;
        while k < glen {
            let id64 = g[k];
            let idus = id64 as usize;
            let p = &conflictingPairs[idus];

            let mut a = p[0];
            if p[1] < a {
                a = p[1];
            }

            if a > max1 {
                max2 = max1;
                max1 = a;
                cnt1 = 1;
                id1 = id64;
            } else if a == max1 {
                cnt1 += 1;
            } else if a > max2 {
                max2 = a;
            }

            k += 1;
        }

        baseline += r - max1;

        if cnt1 == 1 {
            let gain = max1 - max2;
            let gid = id1 as usize;
            gains[gid] += gain;
        }

        r += 1;
    }

    let mut best: i64 = 0;
    let mut idx: usize = 0;
    while idx < gains.len() {
        if gains[idx] > best {
            best = gains[idx];
        }
        idx += 1;
    }

    baseline + best
}
