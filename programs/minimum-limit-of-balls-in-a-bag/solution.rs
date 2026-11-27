pub fn minimum_size(nums: &[i64], maxOperations: i64) -> i64 {
    let n = nums.len();

    let mut high: i64 = 1;
    let mut i: usize = 0;
    while i < n {
        if nums[i] > high {
            high = nums[i];
        }
        i += 1;
    }

    let mut low: i64 = 1;
    while low < high {
        let mid: i64 = low + (high - low) / 2;

        let mut ops: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            ops = ops + (nums[j] - 1) / mid;
            j += 1;
        }

        if ops <= maxOperations {
            high = mid;
        } else {
            low = mid + 1;
        }
    }

    low
}
