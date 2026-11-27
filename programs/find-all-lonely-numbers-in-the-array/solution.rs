fn table_contains(keys: &[i64], m: usize, x: i64) -> bool {
    let mut idx: usize = (x as usize) % m;
    let mut steps: usize = 0;

    while steps < m {
        let k = keys[idx];
        if k == -1 {
            return false;
        }
        if k == x {
            return true;
        }

        idx += 1;
        if idx == m {
            idx = 0;
        }
        steps += 1;
    }

    false
}

pub fn find_lonely(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    let target = n + n + 1;

    let mut m: usize = 1;
    while m < target {
        m = m + m;
    }

    let mut keys: Vec<i64> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();

    let mut j: usize = 0;
    while j < m {
        keys.push(-1);
        counts.push(0);
        j += 1;
    }

    let mut i: usize = 0;
    while i < n {
        let x = nums[i];
        let mut idx: usize = (x as usize) % m;
        let mut steps: usize = 0;

        while steps < m && keys[idx] != -1 && keys[idx] != x {
            idx += 1;
            if idx == m {
                idx = 0;
            }
            steps += 1;
        }

        if keys[idx] == -1 {
            keys[idx] = x;
            counts[idx] = 1;
        } else if keys[idx] == x {
            counts[idx] = counts[idx] + 1;
        }

        i += 1;
    }

    let mut out: Vec<i64> = Vec::new();

    i = 0;
    while i < n {
        let x = nums[i];
        let mut idx: usize = (x as usize) % m;
        let mut steps: usize = 0;

        while steps < m && keys[idx] != -1 && keys[idx] != x {
            idx += 1;
            if idx == m {
                idx = 0;
            }
            steps += 1;
        }

        if keys[idx] == x && counts[idx] == 1 {
            let mut lonely: bool = true;

            if x > 0 {
                if table_contains(&keys, m, x - 1) {
                    lonely = false;
                }
            }

            if lonely {
                if table_contains(&keys, m, x + 1) {
                    lonely = false;
                }
            }

            if lonely {
                out.push(x);
            }
        }

        i += 1;
    }

    out
}
