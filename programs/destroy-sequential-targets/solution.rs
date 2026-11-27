pub fn destroy_targets(nums: &[i64], space: i64) -> i64 {
    let n = nums.len();

    let mut max_val: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i += 1;
    }

    let base: i64 = max_val + 1;

    let mut keys: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        let v = nums[i];
        let r = v % space;
        let key = r * base + v;
        keys.push(key);
        i += 1;
    }

    keys.sort();

    let mut best_count: i64 = 0;
    let mut ans: i64 = 0;
    i = 0;

    while i < n {
        let first_key = keys[i];
        let residue = first_key / base;
        let min_val = first_key % base;

        let mut count: i64 = 0;
        while i < n {
            let cur = keys[i];
            if cur / base != residue {
                break;
            }
            count += 1;
            i += 1;
        }

        if count > best_count {
            best_count = count;
            ans = min_val;
        } else if count == best_count && min_val < ans {
            ans = min_val;
        }
    }

    ans
}
