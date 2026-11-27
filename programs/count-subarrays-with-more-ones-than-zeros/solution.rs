pub fn subarrays_with_more_zeros_than_ones(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    let size: usize = 2 * n + 2;

    let mut bit: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < size {
        bit.push(0);
        z = z + 1;
    }

    let mut ans: i64 = 0;
    let mut pos: usize = n + 1;

    // Insert the empty prefix sum 0.
    let mut i: usize = pos;
    while i < size {
        bit[i] = bit[i] + 1;

        let mut low: usize = 1;
        let mut x: usize = i;
        while x % 2 == 0 {
            low = low * 2;
            x = x / 2;
        }
        i = i + low;
    }

    let mut k: usize = 0;
    while k < n {
        if nums[k] == 1 {
            pos = pos + 1;
        } else {
            pos = pos - 1;
        }

        // Count previous prefix sums strictly smaller than the current one.
        let mut q: usize = pos - 1;
        let mut cnt: i64 = 0;
        while q > 0 {
            cnt = cnt + bit[q];

            let mut low: usize = 1;
            let mut x: usize = q;
            while x % 2 == 0 {
                low = low * 2;
                x = x / 2;
            }
            q = q - low;
        }

        ans = (ans + cnt) % 1000000007;

        // Insert the current prefix sum.
        let mut u: usize = pos;
        while u < size {
            bit[u] = bit[u] + 1;

            let mut low: usize = 1;
            let mut x: usize = u;
            while x % 2 == 0 {
                low = low * 2;
                x = x / 2;
            }
            u = u + low;
        }

        k = k + 1;
    }

    ans
}
