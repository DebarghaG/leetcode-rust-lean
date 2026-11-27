fn count_distinct_range(nums: &[i64], start: usize, end: usize) -> i64 {
    let mut count: i64 = 0;
    let mut p: usize = start;

    while p < end {
        let mut seen: bool = false;
        let mut q: usize = start;

        while q < p {
            if nums[q] == nums[p] {
                seen = true;
            }
            q += 1;
        }

        if !seen {
            count += 1;
        }

        p += 1;
    }

    count
}

pub fn distinct_difference_array(nums: &[i64]) -> Vec<i64> {
    let n: usize = nums.len();
    let mut diff: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < n {
        let prefix_count: i64 = count_distinct_range(nums, 0, i + 1);
        let suffix_count: i64 = count_distinct_range(nums, i + 1, n);
        diff.push(prefix_count - suffix_count);
        i += 1;
    }

    diff
}
