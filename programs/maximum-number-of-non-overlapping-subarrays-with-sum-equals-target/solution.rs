fn hash_index(key: i64, cap: usize) -> usize {
    let mut y: i64 = key + 2000000000;
    y = y ^ (y >> 16);
    y = y ^ (y >> 8);
    y = y ^ (y >> 4);

    let m: i64 = cap as i64;
    let mut v: i64 = y % m;
    if v < 0 {
        v = v + m;
    }
    v as usize
}

fn table_contains(keys: &[i64], stamps: &[i64], key: i64, epoch: i64) -> bool {
    let cap = keys.len();
    let mut idx = hash_index(key, cap);
    let mut steps: usize = 0;

    while steps < cap {
        if stamps[idx] != epoch {
            return false;
        }
        if keys[idx] == key {
            return true;
        }

        idx = idx + 1;
        if idx == cap {
            idx = 0;
        }
        steps = steps + 1;
    }

    false
}

fn table_insert(keys: &mut Vec<i64>, stamps: &mut Vec<i64>, key: i64, epoch: i64) {
    let cap = keys.len();
    let mut idx = hash_index(key, cap);
    let mut steps: usize = 0;

    while steps < cap {
        if stamps[idx] != epoch {
            keys[idx] = key;
            stamps[idx] = epoch;
            return;
        }
        if keys[idx] == key {
            return;
        }

        idx = idx + 1;
        if idx == cap {
            idx = 0;
        }
        steps = steps + 1;
    }
}

pub fn max_non_overlapping(nums: &[i64], target: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let needed: usize = 4 * (n + 1) + 10;
    let mut cap: usize = 1;
    while cap < needed {
        cap = cap * 2;
    }

    let mut keys: Vec<i64> = Vec::new();
    let mut stamps: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < cap {
        keys.push(0);
        stamps.push(0);
        i = i + 1;
    }

    let mut epoch: i64 = 1;
    let mut ans: i64 = 0;
    let mut prefix: i64 = 0;

    table_insert(&mut keys, &mut stamps, 0, epoch);

    let mut j: usize = 0;
    while j < n {
        prefix = prefix + nums[j];
        let need: i64 = prefix - target;

        if table_contains(&keys, &stamps, need, epoch) {
            ans = ans + 1;
            epoch = epoch + 1;
        }

        table_insert(&mut keys, &mut stamps, prefix, epoch);
        j = j + 1;
    }

    ans
}
