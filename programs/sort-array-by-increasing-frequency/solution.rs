pub fn frequency_sort(nums: &[i64]) -> Vec<i64> {
    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 201 {
        counts.push(0);
        i += 1;
    }

    let n = nums.len();
    let mut idx: usize = 0;
    while idx < n {
        let value = nums[idx];
        let count_index = (value + 100) as usize;
        counts[count_index] = counts[count_index] + 1;
        idx += 1;
    }

    let mut result: Vec<i64> = Vec::new();
    let mut freq: i64 = 1;
    while freq <= n as i64 {
        let mut value: i64 = 100;
        while value >= -100 {
            let count_index = (value + 100) as usize;
            if counts[count_index] == freq {
                let mut repeat: i64 = 0;
                while repeat < freq {
                    result.push(value);
                    repeat += 1;
                }
            }
            value -= 1;
        }
        freq += 1;
    }

    result
}
