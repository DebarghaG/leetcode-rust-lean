pub fn beautiful_subarrays(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut max_val: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i += 1;
    }

    let mut size: i64 = 1;
    while size <= max_val {
        size = size * 2;
    }

    let mut freq: Vec<i64> = Vec::new();
    let mut z: i64 = 0;
    while z < size {
        freq.push(0);
        z += 1;
    }
    freq[0] = 1;

    let mut ans: i64 = 0;
    let mut xr: i64 = 0;
    let mut j: usize = 0;
    while j < n {
        xr = xr ^ nums[j];
        let idx: usize = xr as usize;
        let cnt: i64 = freq[idx];
        ans = ans + cnt;
        freq[idx] = cnt + 1;
        j += 1;
    }

    ans
}
