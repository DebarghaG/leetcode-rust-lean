pub fn minimum_subarray_length(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let mut best: i64 = -1;

    let mut i: usize = 0;
    while i < n {
        let mut cur: i64 = 0;
        let mut j: usize = i;

        while j < n {
            cur = cur | nums[j];

            if cur >= k {
                let len: i64 = (j as i64) - (i as i64) + 1;
                if best == -1 || len < best {
                    best = len;
                }
                break;
            }

            j += 1;
        }

        i += 1;
    }

    best
}
