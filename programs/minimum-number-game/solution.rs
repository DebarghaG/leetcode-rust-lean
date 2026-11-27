pub fn number_game(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();

    let mut sorted: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        sorted.push(nums[i]);
        i += 1;
    }

    let mut i = 1;
    while i < n {
        let key = sorted[i];
        let mut j = i;
        while j > 0 && sorted[j - 1] > key {
            sorted[j] = sorted[j - 1];
            j -= 1;
        }
        sorted[j] = key;
        i += 1;
    }

    let mut out: Vec<i64> = Vec::new();
    let mut k = 0;
    while k + 1 < n {
        out.push(sorted[k + 1]);
        out.push(sorted[k]);
        k += 2;
    }

    out
}
