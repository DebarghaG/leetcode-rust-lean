pub fn min_cost(nums: &[i64], cost: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut total: i64 = 0;
    let mut min_v: i64 = nums[0];
    let mut max_v: i64 = nums[0];
    let mut i: usize = 0;
    while i < n {
        total = total + cost[i];
        if nums[i] < min_v {
            min_v = nums[i];
        }
        if nums[i] > max_v {
            max_v = nums[i];
        }
        i = i + 1;
    }

    let target: i64 = (total + 1) / 2;
    let mut lo: i64 = min_v;
    let mut hi: i64 = max_v;

    while lo < hi {
        let mid: i64 = lo + (hi - lo) / 2;
        let mut acc: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            if nums[j] <= mid {
                acc = acc + cost[j];
            }
            j = j + 1;
        }

        if acc >= target {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    let median: i64 = lo;
    let mut ans: i64 = 0;
    i = 0;
    while i < n {
        let mut diff: i64 = nums[i] - median;
        if diff < 0 {
            diff = -diff;
        }
        ans = ans + diff * cost[i];
        i = i + 1;
    }

    ans
}
