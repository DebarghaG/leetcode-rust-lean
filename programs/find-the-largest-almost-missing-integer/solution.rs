pub fn largest_integer(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let kk = k as usize;
    let mut ans: i64 = -1;

    let mut i: usize = 0;
    while i < n {
        let x = nums[i];
        let mut count: i64 = 0;

        let mut start: usize = 0;
        while start + kk <= n {
            let mut found = false;
            let mut j = start;
            while j < start + kk {
                if nums[j] == x {
                    found = true;
                }
                j += 1;
            }

            if found {
                count += 1;
            }

            start += 1;
        }

        if count == 1 && x > ans {
            ans = x;
        }

        i += 1;
    }

    ans
}
