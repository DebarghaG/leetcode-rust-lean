pub fn longest_consecutive(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut sorted: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        sorted.push(nums[i]);
        i += 1;
    }

    sorted.sort();

    let mut best: i64 = 1;
    let mut current: i64 = 1;
    let mut j: usize = 1;

    while j < n {
        let prev = sorted[j - 1];
        let cur = sorted[j];

        if cur == prev {
            // Duplicate values do not change the consecutive run.
        } else if cur == prev + 1 {
            current += 1;
            if current > best {
                best = current;
            }
        } else {
            current = 1;
        }

        j += 1;
    }

    best
}
