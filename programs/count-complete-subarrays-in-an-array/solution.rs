pub fn count_complete_subarrays(nums: &[i64]) -> i64 {
    let n = nums.len();
    let size: usize = 2001;

    let mut freq: Vec<i64> = Vec::new();
    let mut p: usize = 0;
    while p < size {
        freq.push(0);
        p += 1;
    }

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let idx = nums[i] as usize;
        if freq[idx] == 0 {
            freq[idx] = 1;
            total += 1;
        }
        i += 1;
    }

    let mut reset: usize = 0;
    while reset < size {
        freq[reset] = 0;
        reset += 1;
    }

    let mut ans: i64 = 0;
    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut distinct: i64 = 0;

    while right < n {
        let idx = nums[right] as usize;
        if freq[idx] == 0 {
            distinct += 1;
        }
        freq[idx] = freq[idx] + 1;

        while distinct == total {
            let lidx = nums[left] as usize;
            freq[lidx] = freq[lidx] - 1;
            if freq[lidx] == 0 {
                distinct -= 1;
            }
            left += 1;
        }

        ans += left as i64;
        right += 1;
    }

    ans
}
