pub fn sorted_squares(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    let mut out: Vec<i64> = Vec::new();

    if n == 0 {
        return out;
    }

    let mut k: usize = 0;
    while k < n {
        out.push(0);
        k += 1;
    }

    let mut left: usize = 0;
    let mut right: usize = n - 1;
    let mut pos: usize = n;

    while left <= right {
        let left_sq = nums[left] * nums[left];
        let right_sq = nums[right] * nums[right];

        if left_sq > right_sq {
            pos -= 1;
            out[pos] = left_sq;
            left += 1;
        } else {
            pos -= 1;
            out[pos] = right_sq;

            if right == 0 {
                break;
            }
            right -= 1;
        }
    }

    out
}
