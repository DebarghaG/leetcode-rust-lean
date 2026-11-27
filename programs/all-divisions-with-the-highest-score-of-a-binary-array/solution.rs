pub fn max_score_indices(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();

    let mut total_ones: i64 = 0;
    let mut k: usize = 0;
    while k < n {
        if nums[k] == 1 {
            total_ones += 1;
        }
        k += 1;
    }

    let mut best: i64 = -1;

    let mut zeros_left: i64 = 0;
    let mut ones_right: i64 = total_ones;
    let mut i: usize = 0;

    while i <= n {
        let score = zeros_left + ones_right;
        if score > best {
            best = score;
        }

        if i < n {
            if nums[i] == 0 {
                zeros_left += 1;
            } else {
                ones_right -= 1;
            }
        }

        i += 1;
    }

    let mut result: Vec<i64> = Vec::new();

    zeros_left = 0;
    ones_right = total_ones;
    i = 0;

    while i <= n {
        let score = zeros_left + ones_right;
        if score == best {
            result.push(i as i64);
        }

        if i < n {
            if nums[i] == 0 {
                zeros_left += 1;
            } else {
                ones_right -= 1;
            }
        }

        i += 1;
    }

    result
}
