pub fn min_k_bit_flips(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let kk = k as usize;

    let mut flip_start: Vec<i64> = Vec::new();
    let mut p: usize = 0;
    while p < n {
        flip_start.push(0);
        p += 1;
    }

    let mut active_flips: i64 = 0;
    let mut answer: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        if i >= kk {
            active_flips -= flip_start[i - kk];
        }

        let current_bit = nums[i] ^ (active_flips % 2);

        if current_bit == 0 {
            if i + kk > n {
                return -1;
            }

            answer += 1;
            active_flips += 1;
            flip_start[i] = 1;
        }

        i += 1;
    }

    answer
}
