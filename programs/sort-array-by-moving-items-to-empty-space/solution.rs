pub fn sort_array(nums: &[i64]) -> i64 {
    let a = cost(nums, false);
    let b = cost(nums, true);
    if a < b { a } else { b }
}

fn cost(nums: &[i64], zero_at_end: bool) -> i64 {
    let n = nums.len();

    let mut seen: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        seen.push(0);
        i += 1;
    }

    let d: usize = if zero_at_end { n - 1 } else { 0 };

    let mut ans: i64 = 0;
    let mut start: usize = 0;

    while start < n {
        if seen[start] == 0 {
            let mut length: i64 = 0;
            let mut contains_d: bool = false;
            let mut cur: usize = start;

            while seen[cur] == 0 {
                seen[cur] = 1;
                length += 1;

                if cur == d {
                    contains_d = true;
                }

                let val = nums[cur];
                let next: usize;

                if zero_at_end {
                    if val == 0 {
                        next = n - 1;
                    } else {
                        next = (val - 1) as usize;
                    }
                } else {
                    next = val as usize;
                }

                cur = next;
            }

            if length > 1 {
                if contains_d {
                    ans += length - 1;
                } else {
                    ans += length + 1;
                }
            }
        }

        start += 1;
    }

    ans
}
