pub fn min_cost(nums: &[i64], x: i64) -> i64 {
    let n = nums.len();

    let mut cur: Vec<i64> = Vec::new();
    let mut sum: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let v = nums[i];
        cur.push(v);
        sum += v;
        i += 1;
    }

    let mut ans: i64 = sum;

    let mut k: usize = 1;
    let mut k_i64: i64 = 1;

    while k < n {
        let mut j: usize = 0;
        let mut current_sum: i64 = 0;

        while j < n {
            let mut idx = j + k;
            if idx >= n {
                idx -= n;
            }

            let candidate = nums[idx];
            let old = cur[j];

            if candidate < old {
                cur[j] = candidate;
                current_sum += candidate;
            } else {
                current_sum += old;
            }

            j += 1;
        }

        let total = current_sum + k_i64 * x;
        if total < ans {
            ans = total;
        }

        k += 1;
        k_i64 += 1;
    }

    ans
}
