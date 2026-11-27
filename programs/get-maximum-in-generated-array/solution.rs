pub fn get_maximum_generated(n: i64) -> i64 {
    if n <= 0 {
        return 0;
    }
    if n == 1 {
        return 1;
    }

    let len: usize = (n + 1) as usize;

    let mut nums: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < len {
        nums.push(0);
        k += 1;
    }

    nums[0] = 0;
    nums[1] = 1;

    let mut i: usize = 2;
    while i < len {
        let half: usize = i / 2;
        if i % 2 == 0 {
            nums[i] = nums[half];
        } else {
            nums[i] = nums[half] + nums[half + 1];
        }
        i += 1;
    }

    let mut best: i64 = nums[0];
    let mut j: usize = 1;
    while j < len {
        if nums[j] > best {
            best = nums[j];
        }
        j += 1;
    }

    best
}
