pub fn contains_nearby_duplicate(nums: &[i64], k: i64) -> bool {
    let n = nums.len();

    // Open-addressing hash table with linear probing.
    // keys[h] = stored value, last[h] = most recent index of that value (-1 = empty).
    let mut cap: usize = 1;
    let target: usize = n * 2;
    while cap < target {
        cap = cap * 2;
    }

    let mut keys: Vec<i64> = Vec::new();
    let mut last: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < cap {
        keys.push(0);
        last.push(-1);
        j += 1;
    }

    let m = cap as i64;
    let mut i: usize = 0;
    let mut found = false;

    while i < n && !found {
        let v = nums[i];

        let mut hv = v % m;
        if hv < 0 {
            hv += m;
        }
        let mut h = hv as usize;

        let mut placed = false;
        while !placed {
            if last[h] == -1 {
                keys[h] = v;
                last[h] = i as i64;
                placed = true;
            } else if keys[h] == v {
                let prev = last[h];
                let cur = i as i64;
                if cur - prev <= k {
                    found = true;
                } else {
                    last[h] = cur;
                }
                placed = true;
            } else {
                h += 1;
                if h == cap {
                    h = 0;
                }
            }
        }

        i += 1;
    }

    found
}
