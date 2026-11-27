pub fn min_difference(nums: &[i64], queries: &[Vec<i64>]) -> Vec<i64> {
    let n = nums.len();

    let mut positions: Vec<Vec<i64>> = Vec::new();
    let mut v: usize = 0;
    while v <= 100 {
        let mut row: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            if nums[i] == v as i64 {
                row.push(i as i64);
            }
            i += 1;
        }
        positions.push(row);
        v += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let qn = queries.len();
    let mut qi: usize = 0;

    while qi < qn {
        let l_i64 = queries[qi][0];
        let r_i64 = queries[qi][1];

        let mut best: i64 = 1000000;
        let mut prev: i64 = -1;

        let mut value: usize = 0;
        while value <= 100 {
            let row = &positions[value];
            let len = row.len();

            if len > 0 {
                let mut lo: usize = 0;
                let mut hi: usize = len;

                while lo < hi {
                    let mid = lo + (hi - lo) / 2;
                    if row[mid] < l_i64 {
                        lo = mid + 1;
                    } else {
                        hi = mid;
                    }
                }

                if lo < len && row[lo] <= r_i64 {
                    if prev >= 0 {
                        let d = (value as i64) - prev;
                        if d < best {
                            best = d;
                        }
                    }
                    prev = value as i64;
                }
            }

            value += 1;
        }

        if best == 1000000 {
            ans.push(-1);
        } else {
            ans.push(best);
        }

        qi += 1;
    }

    ans
}
