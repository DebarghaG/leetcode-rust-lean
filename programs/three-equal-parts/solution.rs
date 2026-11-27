fn lower_bound(pref: &[i64], target: i64) -> usize {
    let n = pref.len();
    let mut pos: usize = n;
    let mut idx: usize = 0;
    while idx < n {
        if pref[idx] >= target {
            if idx < pos {
                pos = idx;
            }
        }
        idx += 1;
    }
    pos
}

pub fn three_equal_parts(arr: &[i64]) -> Vec<i64> {
    let n = arr.len();

    // Build prefix count of ones: pref[i] = number of ones in arr[0..=i]
    let mut pref: Vec<i64> = Vec::new();
    let mut running: i64 = 0;
    let mut idx: usize = 0;
    while idx < n {
        if arr[idx] == 1 {
            running += 1;
        }
        pref.push(running);
        idx += 1;
    }
    let total: i64 = running;

    let mut ans: Vec<i64> = Vec::new();

    if total == 0 {
        ans.push(0);
        ans.push((n - 1) as i64);
    } else if total % 3 != 0 {
        ans.push(-1);
        ans.push(-1);
    } else {
        let k: i64 = total / 3;

        // Positions of the 1st, (k+1)-th, and (2k+1)-th one.
        let p1: usize = lower_bound(&pref, 1);
        let p2: usize = lower_bound(&pref, k + 1);
        let p3: usize = lower_bound(&pref, 2 * k + 1);

        // Length of the significant part of the third block.
        let l: usize = n - p3;

        let mut ok: bool = true;
        if p1 + l > p2 {
            ok = false;
        }
        if p2 + l > p3 {
            ok = false;
        }

        if ok {
            let mut d: usize = 0;
            while d < l {
                if arr[p1 + d] != arr[p3 + d] || arr[p2 + d] != arr[p3 + d] {
                    ok = false;
                }
                d += 1;
            }
        }

        if ok {
            ans.push((p1 + l - 1) as i64);
            ans.push((p2 + l) as i64);
        } else {
            ans.push(-1);
            ans.push(-1);
        }
    }

    ans
}
