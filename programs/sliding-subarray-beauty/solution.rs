pub fn get_subarray_beauty(nums: &[i64], k: i64, x: i64) -> Vec<i64> {
    let n: usize = nums.len();
    let kk: usize = k as usize;
    let xx: i64 = x;

    let mut ans: Vec<i64> = Vec::new();

    let mut freq: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 50 {
        freq.push(0);
        i += 1;
    }

    let mut j: usize = 0;
    while j < kk {
        let v: i64 = nums[j];
        if v < 0 {
            let idx: usize = (v + 50) as usize;
            freq[idx] = freq[idx] + 1;
        }
        j += 1;
    }

    let windows: usize = n - kk + 1;
    let mut start: usize = 0;

    while start < windows {
        let mut count: i64 = 0;
        let mut value: i64 = 0;
        let mut found: bool = false;

        let mut idx: usize = 0;
        while idx < 50 {
            let f: i64 = freq[idx];
            if f > 0 && !found {
                count = count + f;
                if count >= xx {
                    value = (idx as i64) - 50;
                    found = true;
                }
            }
            idx += 1;
        }

        if found {
            ans.push(value);
        } else {
            ans.push(0);
        }

        if start + 1 < windows {
            let out_v: i64 = nums[start];
            if out_v < 0 {
                let out_idx: usize = (out_v + 50) as usize;
                freq[out_idx] = freq[out_idx] - 1;
            }

            let add_v: i64 = nums[start + kk];
            if add_v < 0 {
                let add_idx: usize = (add_v + 50) as usize;
                freq[add_idx] = freq[add_idx] + 1;
            }
        }

        start += 1;
    }

    ans
}
