pub fn longest_alternating_subarray(nums: &[i64], threshold: i64) -> i64 {
    let n = nums.len();
    let mut best: i64 = 0;
    let mut l: usize = 0;

    while l < n {
        if nums[l] <= threshold && nums[l] % 2 == 0 {
            let mut r: usize = l + 1;
            let mut good: bool = true;

            while r < n && good {
                let prev = nums[r - 1];
                let curr = nums[r];

                if curr <= threshold && curr % 2 != prev % 2 {
                    r += 1;
                } else {
                    good = false;
                }
            }

            let len: i64 = (r - l) as i64;
            if len > best {
                best = len;
            }
        }

        l += 1;
    }

    best
}
