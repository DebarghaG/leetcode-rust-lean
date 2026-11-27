pub fn num_subseq(nums: &[i64], target: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    // Copy the input into an owned vector.
    let mut src: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < n {
        src.push(nums[idx]);
        idx += 1;
    }

    // Iterative bottom-up merge sort, avoiding recursion and iterator chains.
    let mut width: usize = 1;
    while width < n {
        let mut dst: Vec<i64> = Vec::new();
        let mut start: usize = 0;

        while start < n {
            let mid = if start + width < n { start + width } else { n };
            let end = if start + width + width < n {
                start + width + width
            } else {
                n
            };

            let mut i = start;
            let mut j = mid;

            while i < mid && j < end {
                if src[i] <= src[j] {
                    dst.push(src[i]);
                    i += 1;
                } else {
                    dst.push(src[j]);
                    j += 1;
                }
            }

            while i < mid {
                dst.push(src[i]);
                i += 1;
            }

            while j < end {
                dst.push(src[j]);
                j += 1;
            }

            start = end;
        }

        src = dst;
        width = width * 2;
    }

    // Precompute powers of two modulo 1_000_000_007.
    let mut pow2: Vec<i64> = Vec::new();
    let mut p: i64 = 1;
    let mut k: usize = 0;
    while k < n {
        pow2.push(p);
        p = (p * 2) % 1_000_000_007;
        k += 1;
    }

    let mut ans: i64 = 0;
    let mut left: usize = 0;
    let mut right: usize = n - 1;

    while left <= right {
        let sum = src[left] + src[right];

        if sum <= target {
            let exp = right - left;
            ans = ans + pow2[exp];
            ans = ans % 1_000_000_007;
            left += 1;
        } else {
            if right == 0 {
                break;
            }
            right -= 1;
        }
    }

    ans
}
