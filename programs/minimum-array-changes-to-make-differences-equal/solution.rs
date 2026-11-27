pub fn min_changes(nums: &[i64], k: i64) -> i64 {
    let n: usize = nums.len();
    let m: usize = n / 2;

    let mut diffs: Vec<i64> = Vec::new();
    let mut thresh: Vec<i64> = Vec::new();

    let mut p: usize = 0;
    while p < m {
        let a: i64 = nums[p];
        let b: i64 = nums[n - p - 1];

        let mut mn: i64 = a;
        let mut mx: i64 = b;
        if b < a {
            mn = b;
            mx = a;
        }

        let d: i64 = mx - mn;
        let mut t: i64 = mx;
        let other: i64 = k - mn;
        if other > t {
            t = other;
        }

        diffs.push(d);
        thresh.push(t);

        p += 1;
    }

    diffs.sort();
    thresh.sort();

    let m_i: i64 = m as i64;
    let mut best: i64 = m_i;

    let mut ti: usize = 0;
    let mut di: usize = 0;

    while di < m {
        let d: i64 = diffs[di];
        let mut freq: i64 = 0;

        while di < m {
            if diffs[di] == d {
                freq += 1;
                di += 1;
            } else {
                break;
            }
        }

        while ti < m {
            if thresh[ti] < d {
                ti += 1;
            } else {
                break;
            }
        }

        let lt: i64 = ti as i64;
        let cost: i64 = m_i + lt - freq;
        if cost < best {
            best = cost;
        }
    }

    best
}
