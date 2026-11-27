pub fn minimal_k_sum(nums: &[i64], k: i64) -> i64 {
    let mut v: Vec<i64> = Vec::new();
    let n = nums.len();
    let mut i = 0usize;
    while i < n {
        v.push(nums[i]);
        i += 1;
    }
    v.sort();

    let m = v.len();
    let mut ans: i64 = 0;
    let mut need: i64 = k;
    let mut cur: i64 = 1;
    let mut idx: usize = 0;

    while idx < m && need > 0 {
        let x = v[idx];

        if x >= cur {
            let avail = x - cur;
            if avail > 0 {
                let take = if avail < need { avail } else { need };
                ans += take * (2 * cur + take - 1) / 2;
                cur += take;
                need -= take;
            }

            if need > 0 && x == cur {
                cur += 1;
            }
        }

        idx += 1;
    }

    if need > 0 {
        ans += need * (2 * cur + need - 1) / 2;
    }

    ans
}
