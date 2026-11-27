pub fn min_operations(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let kk = k as usize;

    let mut seen: Vec<bool> = Vec::new();
    let mut j = 0usize;
    while j <= kk {
        seen.push(false);
        j += 1;
    }

    let mut count: i64 = 0;
    let mut i = n;

    while i > 0 {
        i -= 1;
        let x = nums[i];

        if x >= 1 && x <= k {
            let xi = x as usize;
            if !seen[xi] {
                seen[xi] = true;
                count += 1;

                if count == k {
                    return (n - i) as i64;
                }
            }
        }
    }

    n as i64
}
