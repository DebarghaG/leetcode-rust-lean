pub fn maximum_length(nums: &[i64], k: i64) -> i64 {
    let n: usize = nums.len();
    let kk: usize = k as usize;

    let mut best: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t <= kk {
        best.push(0);
        t += 1;
    }

    let mut vals: Vec<i64> = Vec::new();
    let mut best_val: Vec<Vec<i64>> = Vec::new();
    let mut ans: i64 = 0;

    let mut ii: usize = 0;
    while ii < n {
        let x: i64 = nums[ii];

        let mut id: usize = 0;
        let mut found: bool = false;
        let d: usize = vals.len();

        while id < d {
            if vals[id] == x {
                found = true;
                break;
            }
            id += 1;
        }

        if !found {
            id = d;
            vals.push(x);

            let mut row: Vec<i64> = Vec::new();
            let mut r: usize = 0;
            while r <= kk {
                row.push(0);
                r += 1;
            }
            best_val.push(row);
        }

        let mut step: usize = 0;
        while step <= kk {
            let j: usize = kk - step;

            let same: i64 = best_val[id][j] + 1;
            let mut cur: i64 = same;

            if j > 0 {
                let diff: i64 = best[j - 1] + 1;
                if diff > cur {
                    cur = diff;
                }
            }

            if cur > best_val[id][j] {
                best_val[id][j] = cur;
            }
            if cur > best[j] {
                best[j] = cur;
            }
            if cur > ans {
                ans = cur;
            }

            step += 1;
        }

        ii += 1;
    }

    ans
}
