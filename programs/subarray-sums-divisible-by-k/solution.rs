pub fn subarrays_div_by_k(nums: &[i64], k: i64) -> i64 {
    if k <= 0 {
        return 0;
    }

    let mut counts: Vec<i64> = Vec::new();
    let mut j: i64 = 0;
    while j < k {
        counts.push(0);
        j += 1;
    }
    counts[0] = 1;

    let mut prefix_rem: i64 = 0;
    let mut answer: i64 = 0;
    let mut i: usize = 0;

    while i < nums.len() {
        prefix_rem = (prefix_rem + nums[i]) % k;
        if prefix_rem < 0 {
            prefix_rem += k;
        }

        let idx: usize = prefix_rem as usize;
        answer += counts[idx];
        counts[idx] = counts[idx] + 1;

        i += 1;
    }

    answer
}
