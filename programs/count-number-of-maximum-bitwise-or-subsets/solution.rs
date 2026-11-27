pub fn count_max_or_subsets(nums: &[i64]) -> i64 {
    let n: usize = nums.len();

    let mut target: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        target = target | nums[i];
        i += 1;
    }

    let mut powers: Vec<i64> = Vec::new();
    let mut p: i64 = 1;
    let mut k: usize = 0;
    while k < n {
        powers.push(p);
        p = p * 2;
        k += 1;
    }

    let mut count: i64 = 0;
    let mut mask: i64 = 1;
    while mask < p {
        let mut cur: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            if (mask & powers[j]) != 0 {
                cur = cur | nums[j];
            }
            j += 1;
        }
        if cur == target {
            count += 1;
        }
        mask += 1;
    }

    count
}
