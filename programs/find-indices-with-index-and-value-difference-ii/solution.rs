pub fn find_indices(nums: &[i64], indexDifference: i64, valueDifference: i64) -> Vec<i64> {
    let n: usize = nums.len();
    let d: usize = indexDifference as usize;

    let mut found: bool = false;
    let mut ri: i64 = -1;
    let mut rj: i64 = -1;

    let mut min_val: i64 = nums[0];
    let mut min_idx: usize = 0;
    let mut max_val: i64 = nums[0];
    let mut max_idx: usize = 0;

    let mut i: usize = d;
    while i < n && !found {
        let k: usize = i - d;
        if k > 0 {
            let v: i64 = nums[k];
            if v < min_val {
                min_val = v;
                min_idx = k;
            }
            if v > max_val {
                max_val = v;
                max_idx = k;
            }
        }

        let cur: i64 = nums[i];

        if cur - min_val >= valueDifference {
            found = true;
            ri = min_idx as i64;
            rj = i as i64;
        } else if max_val - cur >= valueDifference {
            found = true;
            ri = max_idx as i64;
            rj = i as i64;
        } else {
            i += 1;
        }
    }

    let mut ans: Vec<i64> = Vec::new();
    ans.push(ri);
    ans.push(rj);
    ans
}
