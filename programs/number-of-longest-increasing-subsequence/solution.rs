pub fn find_number_of_lis(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut lengths: Vec<i64> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        lengths.push(1);
        counts.push(1);

        let mut j: usize = 0;
        while j < i {
            if nums[j] < nums[i] {
                let candidate = lengths[j] + 1;
                if candidate > lengths[i] {
                    lengths[i] = candidate;
                    counts[i] = counts[j];
                } else if candidate == lengths[i] {
                    counts[i] = counts[i] + counts[j];
                }
            }
            j += 1;
        }

        i += 1;
    }

    let mut best: i64 = 0;
    i = 0;
    while i < n {
        if lengths[i] > best {
            best = lengths[i];
        }
        i += 1;
    }

    let mut answer: i64 = 0;
    i = 0;
    while i < n {
        if lengths[i] == best {
            answer += counts[i];
        }
        i += 1;
    }

    answer
}
