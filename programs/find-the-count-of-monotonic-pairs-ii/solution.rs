pub fn count_of_pairs(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 1;
    }

    let md: i64 = 1000000007;

    let first_max = nums[0] as usize;
    let mut prev: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i <= first_max {
        prev.push(1);
        i += 1;
    }

    let mut idx = 1usize;
    while idx < n {
        let cur_max = nums[idx] as usize;

        let mut pref: Vec<i64> = Vec::new();
        let mut running: i64 = 0;
        let mut j = 0usize;
        while j < prev.len() {
            running = running + prev[j];
            if running >= md {
                running -= md;
            }
            pref.push(running);
            j += 1;
        }

        let diff = nums[idx - 1] - nums[idx];
        let mut cur: Vec<i64> = Vec::new();
        let mut x = 0usize;
        while x <= cur_max {
            let mut limit: i64 = x as i64;
            if diff < 0 {
                limit = limit + diff;
            }

            if limit < 0 {
                cur.push(0);
            } else {
                cur.push(pref[limit as usize]);
            }

            x += 1;
        }

        prev = cur;
        idx += 1;
    }

    let mut ans: i64 = 0;
    let mut k = 0usize;
    while k < prev.len() {
        ans = ans + prev[k];
        if ans >= md {
            ans -= md;
        }
        k += 1;
    }

    ans
}
