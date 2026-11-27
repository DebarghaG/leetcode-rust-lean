pub fn maximum_subarray_sum(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();

    if k <= 0 {
        return 0;
    }

    let k_usize = k as usize;
    if k_usize > n {
        return 0;
    }

    let mut max_val: i64 = 0;
    let mut i = 0;
    while i < n {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i += 1;
    }

    let freq_len = (max_val + 1) as usize;
    let mut freq: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < freq_len {
        freq.push(0);
        j += 1;
    }

    let mut left = 0;
    let mut right = 0;
    let mut distinct: i64 = 0;
    let mut sum: i64 = 0;
    let mut best: i64 = 0;

    while right < n {
        let v = nums[right];
        let idx = v as usize;

        if freq[idx] == 0 {
            distinct += 1;
        }
        freq[idx] += 1;
        sum += v;

        while right - left + 1 > k_usize {
            let lv = nums[left];
            let li = lv as usize;

            freq[li] -= 1;
            if freq[li] == 0 {
                distinct -= 1;
            }
            sum -= lv;
            left += 1;
        }

        if right - left + 1 == k_usize && distinct == k {
            if sum > best {
                best = sum;
            }
        }

        right += 1;
    }

    best
}
