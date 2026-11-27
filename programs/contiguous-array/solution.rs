pub fn find_max_length(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    let size: usize = 2 * n + 1;

    let mut first: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < size {
        first.push(-2);
        k += 1;
    }

    let offset: i64 = n as i64;
    first[n] = -1;

    let mut balance: i64 = 0;
    let mut answer: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        if nums[i] == 1 {
            balance += 1;
        } else {
            balance -= 1;
        }

        let idx: usize = (balance + offset) as usize;
        let previous: i64 = first[idx];
        let current: i64 = i as i64;

        if previous == -2 {
            first[idx] = current;
        } else {
            let length: i64 = current - previous;
            if length > answer {
                answer = length;
            }
        }

        i += 1;
    }

    answer
}
