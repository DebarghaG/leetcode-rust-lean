pub fn number_of_pairs(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();

    let mut seen: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < n {
        seen.push(false);
        i += 1;
    }

    let mut pairs: i64 = 0;
    let mut leftovers: i64 = 0;

    let mut i = 0;
    while i < n {
        if !seen[i] {
            let value = nums[i];
            let mut count: i64 = 0;

            let mut j = 0;
            while j < n {
                if nums[j] == value {
                    count += 1;
                    seen[j] = true;
                }
                j += 1;
            }

            pairs += count / 2;
            leftovers += count % 2;
        }
        i += 1;
    }

    let mut answer: Vec<i64> = Vec::new();
    answer.push(pairs);
    answer.push(leftovers);
    answer
}
