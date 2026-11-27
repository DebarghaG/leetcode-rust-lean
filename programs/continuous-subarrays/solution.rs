pub fn continuous_subarrays(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut minq: Vec<i64> = Vec::new();
    let mut maxq: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        minq.push(0);
        maxq.push(0);
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut left: usize = 0;

    let mut min_head: usize = 0;
    let mut min_tail: usize = 0;
    let mut max_head: usize = 0;
    let mut max_tail: usize = 0;

    let mut right: usize = 0;
    while right < n {
        let x = nums[right];

        while min_tail > min_head {
            let last_idx = minq[min_tail - 1] as usize;
            if nums[last_idx] >= x {
                min_tail -= 1;
            } else {
                break;
            }
        }
        minq[min_tail] = right as i64;
        min_tail += 1;

        while max_tail > max_head {
            let last_idx = maxq[max_tail - 1] as usize;
            if nums[last_idx] <= x {
                max_tail -= 1;
            } else {
                break;
            }
        }
        maxq[max_tail] = right as i64;
        max_tail += 1;

        while nums[maxq[max_head] as usize] - nums[minq[min_head] as usize] > 2 {
            let removed = left;
            left += 1;

            if minq[min_head] as usize == removed {
                min_head += 1;
            }
            if maxq[max_head] as usize == removed {
                max_head += 1;
            }
        }

        ans += (right - left + 1) as i64;
        right += 1;
    }

    ans
}
