pub fn find_smallest_integer(nums: &[i64], value: i64) -> i64 {
    let n_usize: usize = nums.len();
    let n_i64: i64 = n_usize as i64;

    if n_usize == 0 {
        return 0;
    }

    // We only ever need residues that can correspond to a target value < n.
    // Using min(value, n) keeps the table bounded by the input length rather
    // than by a potentially huge `value`.
    let cap: usize = if value < n_i64 {
        value as usize
    } else {
        n_usize
    };
    let cap_i64: i64 = cap as i64;

    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < cap {
        counts.push(0);
        i += 1;
    }

    let mut j: usize = 0;
    while j < n_usize {
        let mut r: i64 = nums[j] % value;
        if r < 0 {
            r += value;
        }
        if r < cap_i64 {
            let idx: usize = r as usize;
            counts[idx] += 1;
        }
        j += 1;
    }

    let mut mex: i64 = 0;
    while mex < n_i64 {
        let idx: usize = (mex % value) as usize;
        if counts[idx] == 0 {
            break;
        }
        counts[idx] -= 1;
        mex += 1;
    }

    mex
}
