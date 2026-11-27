pub fn max_subarray_sum_circular(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let first = nums[0];

    let mut cur_max: i64 = first;
    let mut best_max: i64 = first;

    let mut cur_min: i64 = first;
    let mut best_min: i64 = first;

    let mut total: i64 = first;

    let mut i: usize = 1;
    while i < n {
        let x = nums[i];
        total = total + x;

        let cm = cur_max + x;
        if x > cm {
            cur_max = x;
        } else {
            cur_max = cm;
        }
        if cur_max > best_max {
            best_max = cur_max;
        }

        let cn = cur_min + x;
        if x < cn {
            cur_min = x;
        } else {
            cur_min = cn;
        }
        if cur_min < best_min {
            best_min = cur_min;
        }

        i = i + 1;
    }

    if best_max < 0 {
        return best_max;
    }

    let wrap = total - best_min;
    if best_max > wrap {
        best_max
    } else {
        wrap
    }
}
