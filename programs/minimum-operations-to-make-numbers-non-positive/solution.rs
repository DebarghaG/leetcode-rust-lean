pub fn min_operations(nums: &[i64], x: i64, y: i64) -> i64 {
    let n = nums.len();

    let mut high: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if nums[i] > high {
            high = nums[i];
        }
        i += 1;
    }

    let mut low: i64 = 0;
    while low < high {
        let mid = low + (high - low) / 2;
        if can_finish(nums, x, y, mid) {
            high = mid;
        } else {
            low = mid + 1;
        }
    }

    low
}

fn can_finish(nums: &[i64], x: i64, y: i64, k: i64) -> bool {
    let d = x - y;
    let base = k * y;
    let n = nums.len();

    let mut required: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let need = nums[i] - base;
        if need > 0 {
            let cnt = (need + d - 1) / d;
            required += cnt;
            if required > k {
                return false;
            }
        }
        i += 1;
    }

    required <= k
}
