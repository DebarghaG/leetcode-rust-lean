pub fn get_averages(nums: &[i64], k: i64) -> Vec<i64> {
    let n = nums.len();
    let mut res: Vec<i64> = Vec::new();

    let mut idx: usize = 0;
    while idx < n {
        res.push(-1);
        idx += 1;
    }

    if k < 0 {
        return res;
    }

    let ku = k as usize;
    let win = 2 * ku + 1;

    if n < win {
        return res;
    }

    let mut sum: i64 = 0;
    let mut j: usize = 0;
    while j < win {
        sum += nums[j];
        j += 1;
    }

    let win_i = win as i64;
    let mut center = ku;
    res[center] = sum / win_i;

    center += 1;
    while center + ku < n {
        sum += nums[center + ku];
        sum -= nums[center - ku - 1];
        res[center] = sum / win_i;
        center += 1;
    }

    res
}
