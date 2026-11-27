pub fn count_subarrays(nums: &[i64], k: i64) -> i64 {
    let mut prev_vals: Vec<i64> = Vec::new();
    let mut prev_counts: Vec<i64> = Vec::new();
    let mut ans: i64 = 0;

    let n = nums.len();
    let mut i: usize = 0;

    while i < n {
        let x = nums[i];

        let mut curr_vals: Vec<i64> = Vec::new();
        let mut curr_counts: Vec<i64> = Vec::new();

        let mut pending_val: i64 = x;
        let mut pending_count: i64 = 1;

        let m = prev_vals.len();
        let mut j: usize = 0;

        while j < m {
            let nv = prev_vals[j] & x;
            let c = prev_counts[j];

            if nv == pending_val {
                pending_count = pending_count + c;
            } else {
                curr_vals.push(pending_val);
                curr_counts.push(pending_count);
                pending_val = nv;
                pending_count = c;
            }

            j += 1;
        }

        curr_vals.push(pending_val);
        curr_counts.push(pending_count);

        let q = curr_vals.len();
        let mut t: usize = 0;

        while t < q {
            if curr_vals[t] == k {
                ans += curr_counts[t];
            }
            t += 1;
        }

        prev_vals = curr_vals;
        prev_counts = curr_counts;

        i += 1;
    }

    ans
}
