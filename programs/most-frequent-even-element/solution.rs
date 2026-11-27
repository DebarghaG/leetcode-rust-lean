pub fn most_frequent_even(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut best_val: i64 = -1;
    let mut best_count: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let x = nums[i];
        if x % 2 == 0 {
            let mut cnt: i64 = 0;

            let mut j: usize = 0;
            while j < n {
                if nums[j] == x {
                    cnt += 1;
                }
                j += 1;
            }

            if cnt > best_count
                || (cnt == best_count && (best_val == -1 || x < best_val))
            {
                best_count = cnt;
                best_val = x;
            }
        }

        i += 1;
    }

    best_val
}
