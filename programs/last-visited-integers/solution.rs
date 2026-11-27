pub fn last_visited_integers(nums: &[i64]) -> Vec<i64> {
    let mut seen: Vec<i64> = Vec::new();
    let mut ans: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    let mut i: usize = 0;

    while i < nums.len() {
        let x = nums[i];

        if x == -1 {
            k = k + 1;
            if k <= seen.len() {
                let idx = seen.len() - k;
                ans.push(seen[idx]);
            } else {
                ans.push(-1);
            }
        } else {
            seen.push(x);
            k = 0;
        }

        i = i + 1;
    }

    ans
}
