pub fn maximum_unique_subarray(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    // Small fixed bitset over value / 64. Values are bounded by 10^4,
    // so 160 i64 words are enough and this avoids a large value-sized Vec.
    let mut bits: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < 160 {
        bits.push(0i64);
        i += 1;
    }

    let mut left = 0usize;
    let mut right = 0usize;
    let mut current_sum = 0i64;
    let mut best = 0i64;

    while right < n {
        let v = nums[right];
        let idx = (v / 64) as usize;
        let bit = (v % 64) as usize;
        let mask = 1i64 << bit;

        while (bits[idx] & mask) != 0 {
            let lv = nums[left];
            let lidx = (lv / 64) as usize;
            let lbit = (lv % 64) as usize;
            let lmask = 1i64 << lbit;

            bits[lidx] = bits[lidx] ^ lmask;
            current_sum -= lv;
            left += 1;
        }

        bits[idx] = bits[idx] | mask;
        current_sum += v;

        if current_sum > best {
            best = current_sum;
        }

        right += 1;
    }

    best
}
