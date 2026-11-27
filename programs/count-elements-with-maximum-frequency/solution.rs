pub fn max_frequency_elements(nums: &[i64]) -> i64 {
    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 101 {
        counts.push(0);
        i = i + 1;
    }

    i = 0;
    while i < nums.len() {
        let v: i64 = nums[i];
        if v >= 1 && v <= 100 {
            let idx: usize = v as usize;
            counts[idx] = counts[idx] + 1;
        }
        i = i + 1;
    }

    let mut max_freq: i64 = 0;
    i = 0;
    while i < counts.len() {
        if counts[i] > max_freq {
            max_freq = counts[i];
        }
        i = i + 1;
    }

    let mut total: i64 = 0;
    i = 0;
    while i < counts.len() {
        if counts[i] == max_freq {
            total = total + counts[i];
        }
        i = i + 1;
    }

    total
}
