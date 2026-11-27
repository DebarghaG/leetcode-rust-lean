pub fn total_steps(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut vals: Vec<i64> = Vec::new();
    let mut steps: Vec<i64> = Vec::new();
    let mut ans: i64 = 0;

    let mut i: usize = n;
    while i > 0 {
        i -= 1;
        let v = nums[i];
        let mut cnt: i64 = 0;

        while vals.len() > 0 {
            let last = vals.len() - 1;
            let top = vals[last];

            if v > top {
                let s = steps[last];
                let candidate = cnt + 1;

                if candidate > s {
                    cnt = candidate;
                } else {
                    cnt = s;
                }

                vals.pop();
                steps.pop();
            } else {
                break;
            }
        }

        vals.push(v);
        steps.push(cnt);

        if cnt > ans {
            ans = cnt;
        }
    }

    ans
}
