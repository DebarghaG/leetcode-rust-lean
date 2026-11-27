pub fn smallest_subarrays(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    let bits = 64usize;

    let mut pos: Vec<i64> = Vec::new();
    let mut b = 0usize;
    while b < bits {
        pos.push(-1);
        b += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut k = 0usize;
    while k < n {
        ans.push(0);
        k += 1;
    }

    let mut i = n;
    while i > 0 {
        i -= 1;
        let x = nums[i];

        let mut y = x;
        let mut bit_idx = 0usize;
        while y > 0 {
            if y % 2 == 1 {
                pos[bit_idx] = i as i64;
            }
            y = y / 2;
            bit_idx += 1;
        }

        let mut far = i as i64;
        let mut t = 0usize;
        while t < bits {
            let p = pos[t];
            if p >= 0 && p > far {
                far = p;
            }
            t += 1;
        }

        ans[i] = far - (i as i64) + 1;
    }

    ans
}
