pub fn good_indices(nums: &[i64], k: i64) -> Vec<i64> {
    let n = nums.len();
    let kk = k as usize;

    // left[i] = length of the longest non-increasing contiguous subarray ending at i.
    let mut left: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        if i == 0 {
            left.push(1);
        } else {
            if nums[i - 1] >= nums[i] {
                let prev = left[i - 1];
                left.push(prev + 1);
            } else {
                left.push(1);
            }
        }
        i += 1;
    }

    // right[i] = length of the longest non-decreasing contiguous subarray starting at i.
    let mut right: Vec<i64> = Vec::new();
    let mut z = 0;
    while z < n {
        right.push(0);
        z += 1;
    }

    let mut idx = 0;
    while idx < n {
        let j = n - 1 - idx;
        if j == n - 1 {
            right[j] = 1;
        } else {
            if nums[j] <= nums[j + 1] {
                let nxt = right[j + 1];
                right[j] = nxt + 1;
            } else {
                right[j] = 1;
            }
        }
        idx += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut p = kk;
    let limit = n - kk;
    while p < limit {
        if left[p - 1] >= k && right[p + 1] >= k {
            ans.push(p as i64);
        }
        p += 1;
    }

    ans
}
