pub fn min_operations(nums: &[i64], target: i64) -> i64 {
    let mut cnt: Vec<i64> = Vec::new();
    let mut p: usize = 0;
    while p < 33 {
        cnt.push(0);
        p = p + 1;
    }

    let mut idx: usize = 0;
    while idx < nums.len() {
        let mut x: i64 = nums[idx];
        let mut e: usize = 0;
        while x > 1 {
            x = x / 2;
            e = e + 1;
        }
        cnt[e] = cnt[e] + 1;
        idx = idx + 1;
    }

    let mut ans: i64 = 0;
    let mut rem: i64 = target;
    let mut i: usize = 0;

    while i < 31 {
        let bit: i64 = rem % 2;
        rem = rem / 2;

        if bit == 1 {
            if cnt[i] == 0 {
                let mut j: usize = i + 1;
                while j < 33 && cnt[j] == 0 {
                    j = j + 1;
                }

                if j == 33 {
                    return -1;
                }

                while j > i {
                    cnt[j] = cnt[j] - 1;
                    cnt[j - 1] = cnt[j - 1] + 2;
                    ans = ans + 1;
                    j = j - 1;
                }
            }

            cnt[i] = cnt[i] - 1;
        }

        cnt[i + 1] = cnt[i + 1] + cnt[i] / 2;
        i = i + 1;
    }

    ans
}
