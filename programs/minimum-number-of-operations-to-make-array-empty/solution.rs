pub fn min_operations(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    if n == 0 {
        return 0;
    }

    // A small hash table whose size depends only on the number of elements,
    // never on the magnitude of the values in nums.
    let cap: usize = n * 2 + 1;
    let cap_i: i64 = cap as i64;

    let mut keys: Vec<i64> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();

    let mut t: usize = 0;
    while t < cap {
        keys.push(0);
        counts.push(0);
        t += 1;
    }

    let mut i: usize = 0;
    while i < n {
        let val: i64 = nums[i];
        let mut pos: usize = (val % cap_i) as usize;
        let mut placed: bool = false;

        while !placed {
            if counts[pos] == 0 {
                keys[pos] = val;
                counts[pos] = 1;
                placed = true;
            } else if keys[pos] == val {
                counts[pos] = counts[pos] + 1;
                placed = true;
            } else {
                pos += 1;
                if pos == cap {
                    pos = 0;
                }
            }
        }

        i += 1;
    }

    let mut ans: i64 = 0;
    let mut p: usize = 0;
    while p < cap {
        let count: i64 = counts[p];
        if count > 0 {
            if count == 1 {
                return -1;
            }
            ans += (count + 2) / 3;
        }
        p += 1;
    }

    ans
}
