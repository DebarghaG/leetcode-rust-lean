pub fn count_bad_pairs(nums: &[i64]) -> i64 {
    let n: usize = nums.len();

    let mut cap: usize = 1;
    while cap < 2 * n + 1 {
        cap = cap * 2;
    }

    let mut keys: Vec<i64> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();

    let mut t: usize = 0;
    while t < cap {
        keys.push(0);
        counts.push(0);
        t += 1;
    }

    let mask: usize = cap - 1;
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let key: i64 = nums[i] - (i as i64);
        let mut pos: usize = ((key + 100000) as usize) & mask;
        let mut eq: i64 = 0;
        let mut done: bool = false;

        while !done {
            if counts[pos] == 0 {
                keys[pos] = key;
                counts[pos] = 1;
                done = true;
            } else if keys[pos] == key {
                eq = counts[pos];
                counts[pos] = counts[pos] + 1;
                done = true;
            } else {
                pos = (pos + 1) & mask;
            }
        }

        ans = ans + (i as i64) - eq;
        i += 1;
    }

    ans
}
