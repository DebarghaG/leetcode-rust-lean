pub fn min_moves(nums: &[i64], k: i64) -> i64 {
    let mut positions: Vec<i64> = Vec::new();
    let n = nums.len();

    let mut idx: usize = 0;
    while idx < n {
        if nums[idx] == 1 {
            positions.push(idx as i64);
        }
        idx += 1;
    }

    let m = positions.len();
    let kk = k as usize;

    if kk > m || kk == 0 {
        return 0;
    }

    let mut q: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < m {
        let value = positions[j] - (j as i64);
        q.push(value);
        j += 1;
    }

    let mut prefix: Vec<i64> = Vec::new();
    prefix.push(0);

    j = 0;
    while j < m {
        let value = prefix[j] + q[j];
        prefix.push(value);
        j += 1;
    }

    let mut best: i64 = 1_000_000_000_000_000_000;
    let mut start: usize = 0;

    while start + kk <= m {
        let mid = start + kk / 2;
        let median = q[mid];

        let left_count = (mid - start) as i64;
        let left_sum = prefix[mid] - prefix[start];

        let right_start = mid + 1;
        let right_end = start + kk;
        let right_count = (right_end - right_start) as i64;
        let right_sum = prefix[right_end] - prefix[right_start];

        let cost = median * left_count - left_sum
            + right_sum
            - median * right_count;

        if cost < best {
            best = cost;
        }

        start += 1;
    }

    best
}
