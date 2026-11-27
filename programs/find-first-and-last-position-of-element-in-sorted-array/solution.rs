pub fn search_range(nums: &[i64], target: i64) -> Vec<i64> {
    let n = nums.len();
    let mut res: Vec<i64> = Vec::new();

    let mut lo: usize = 0;
    let mut hi: usize = n;

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if nums[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    let first = lo;

    if first >= n {
        res.push(-1);
        res.push(-1);
        return res;
    }

    if nums[first] != target {
        res.push(-1);
        res.push(-1);
        return res;
    }

    lo = 0;
    hi = n;

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if nums[mid] <= target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    let last = if lo > 0 { lo - 1 } else { 0 };

    res.push(first as i64);
    res.push(last as i64);
    res
}
