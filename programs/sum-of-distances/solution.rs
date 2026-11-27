pub fn distance(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();

    let mut ans: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        ans.push(0);
        i += 1;
    }

    if n == 0 {
        return ans;
    }

    let base: i64 = n as i64 + 1;

    let mut order: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        order.push(nums[i] * base + i as i64);
        i += 1;
    }
    order.sort();

    let mut start: usize = 0;
    while start < n {
        let first_value = order[start] / base;
        let mut end: usize = start + 1;

        while end < n {
            if order[end] / base != first_value {
                break;
            }
            end += 1;
        }

        let m = end - start;

        let mut prefix: i64 = 0;
        let mut k: usize = 0;
        while k < m {
            let key = order[start + k];
            let idx = (key % base) as usize;
            let pos = idx as i64;

            ans[idx] += (k as i64) * pos - prefix;
            prefix += pos;

            k += 1;
        }

        let mut suffix: i64 = 0;
        let mut count_after: i64 = 0;
        let mut r: usize = m;

        while r > 0 {
            r -= 1;

            let key = order[start + r];
            let idx = (key % base) as usize;
            let pos = idx as i64;

            ans[idx] += suffix - count_after * pos;

            suffix += pos;
            count_after += 1;
        }

        start = end;
    }

    ans
}
