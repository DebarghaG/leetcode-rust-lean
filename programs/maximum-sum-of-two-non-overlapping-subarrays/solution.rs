pub fn max_sum_two_no_overlap(nums: &[i64], firstLen: i64, secondLen: i64) -> i64 {
    let n: usize = nums.len();
    let first_len: usize = firstLen as usize;
    let second_len: usize = secondLen as usize;

    let mut prefix: Vec<i64> = Vec::new();
    prefix.push(0);

    let mut i: usize = 0;
    while i < n {
        let next: i64 = prefix[i] + nums[i];
        prefix.push(next);
        i += 1;
    }

    let mut best: i64 = 0;

    let mut start_first: usize = 0;
    while start_first + first_len <= n {
        let sum_first: i64 = prefix[start_first + first_len] - prefix[start_first];

        let mut start_second: usize = 0;
        while start_second + second_len <= n {
            if start_first + first_len <= start_second
                || start_second + second_len <= start_first
            {
                let sum_second: i64 =
                    prefix[start_second + second_len] - prefix[start_second];
                let total: i64 = sum_first + sum_second;

                if total > best {
                    best = total;
                }
            }

            start_second += 1;
        }

        start_first += 1;
    }

    best
}
