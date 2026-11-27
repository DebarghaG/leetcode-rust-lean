pub fn max_sum(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut ans: i64 = -1;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i + 1;

        while j < n {
            let di = largest_digit(nums[i]);
            let dj = largest_digit(nums[j]);

            if di == dj {
                let sum = nums[i] + nums[j];
                if sum > ans {
                    ans = sum;
                }
            }

            j += 1;
        }

        i += 1;
    }

    ans
}

fn largest_digit(mut x: i64) -> i64 {
    let mut best: i64 = 0;

    while x > 0 {
        let d = x % 10;
        if d > best {
            best = d;
        }
        x = x / 10;
    }

    best
}
