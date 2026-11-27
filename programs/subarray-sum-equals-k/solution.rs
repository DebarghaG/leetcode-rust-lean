fn hash_index(key: i64, cap: usize) -> usize {
    let cap_i: i64 = cap as i64;
    let mut r: i64 = key % cap_i;
    if r < 0 {
        r = r + cap_i;
    }
    r as usize
}

pub fn subarray_sum(nums: &[i64], k: i64) -> i64 {
    let n: usize = nums.len();

    // A power-of-two table size with load factor at most 1/2.
    let mut cap: usize = 1;
    let target: usize = (n + 1) * 2;
    while cap < target {
        cap = cap * 2;
    }

    let mut keys: Vec<i64> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();

    let mut z: usize = 0;
    while z < cap {
        keys.push(0);
        counts.push(0);
        z = z + 1;
    }

    // Insert the empty-prefix sum 0 with frequency 1.
    let idx_init: usize = hash_index(0, cap);
    keys[idx_init] = 0;
    counts[idx_init] = 1;

    let mut ans: i64 = 0;
    let mut sum: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        sum = sum + nums[i];
        let need: i64 = sum - k;

        // Look up the frequency of `need` in the hash table.
        let mut idx: usize = hash_index(need, cap);
        let mut found: bool = false;
        while !found {
            if counts[idx] == 0 {
                found = true;
            } else if keys[idx] == need {
                ans = ans + counts[idx];
                found = true;
            } else {
                idx = idx + 1;
                if idx == cap {
                    idx = 0;
                }
            }
        }

        // Insert or increment the current prefix sum.
        let key: i64 = sum;
        let mut idx2: usize = hash_index(key, cap);
        let mut done: bool = false;
        while !done {
            if counts[idx2] == 0 {
                keys[idx2] = key;
                counts[idx2] = 1;
                done = true;
            } else if keys[idx2] == key {
                counts[idx2] = counts[idx2] + 1;
                done = true;
            } else {
                idx2 = idx2 + 1;
                if idx2 == cap {
                    idx2 = 0;
                }
            }
        }

        i = i + 1;
    }

    ans
}
