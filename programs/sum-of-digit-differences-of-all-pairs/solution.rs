pub fn sum_digit_differences(nums: &[i64]) -> i64 {
    let n_usize = nums.len();
    let n = n_usize as i64;
    let total_pairs = n * (n - 1) / 2;

    let mut x = nums[0];
    let mut digits: i64 = 0;
    while x > 0 {
        digits += 1;
        x = x / 10;
    }

    let mut counts: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < 10 {
        counts.push(0);
        t += 1;
    }

    let mut result: i64 = 0;
    let mut place: i64 = 1;
    let mut pos: i64 = 0;

    while pos < digits {
        let mut k: usize = 0;
        while k < 10 {
            counts[k] = 0;
            k += 1;
        }

        let mut i: usize = 0;
        while i < n_usize {
            let digit = (nums[i] / place) % 10;
            let idx = digit as usize;
            counts[idx] = counts[idx] + 1;
            i += 1;
        }

        let mut equal_pairs: i64 = 0;
        let mut j: usize = 0;
        while j < 10 {
            let c = counts[j];
            equal_pairs += c * (c - 1) / 2;
            j += 1;
        }

        result += total_pairs - equal_pairs;
        place *= 10;
        pos += 1;
    }

    result
}
