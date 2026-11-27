pub fn ways_to_split_array(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut total: i64 = 0;
    let mut j: usize = 0;
    while j < n {
        total += nums[j];
        j += 1;
    }

    let mut prefix: i64 = 0;
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i + 1 < n {
        prefix += nums[i];
        let suffix = total - prefix;
        if prefix >= suffix {
            count += 1;
        }
        i += 1;
    }

    count
}
