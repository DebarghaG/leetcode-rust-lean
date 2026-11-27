pub fn minimum_subarray_length(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return -1;
    }
    if k == 0 {
        return 1;
    }

    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 63 {
        counts.push(0);
        i += 1;
    }

    let mut cur_or: i64 = 0;
    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut ans: i64 = -1;

    while right < n {
        let x = nums[right];
        cur_or = cur_or | x;

        let mut b: usize = 0;
        while b < 63 {
            if ((x >> b) & 1) == 1 {
                counts[b] = counts[b] + 1;
            }
            b += 1;
        }

        while left <= right && cur_or >= k {
            let len = (right - left + 1) as i64;
            if ans < 0 || len < ans {
                ans = len;
            }

            let y = nums[left];
            let mut c: usize = 0;
            while c < 63 {
                if ((y >> c) & 1) == 1 {
                    counts[c] = counts[c] - 1;
                    if counts[c] == 0 {
                        cur_or = cur_or - (1i64 << c);
                    }
                }
                c += 1;
            }

            left += 1;
        }

        right += 1;
    }

    ans
}
