pub fn max_div_score(nums: &[i64], divisors: &[i64]) -> i64 {
    let n = nums.len();
    let m = divisors.len();

    let mut best_div: i64 = divisors[0];
    let mut best_score: i64 = -1;

    let mut i: usize = 0;
    while i < m {
        let d = divisors[i];
        let mut score: i64 = 0;

        let mut j: usize = 0;
        while j < n {
            if nums[j] % d == 0 {
                score += 1;
            }
            j += 1;
        }

        if score > best_score || (score == best_score && d < best_div) {
            best_score = score;
            best_div = d;
        }

        i += 1;
    }

    best_div
}
