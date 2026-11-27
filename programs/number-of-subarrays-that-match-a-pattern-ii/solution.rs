pub fn count_matching_subarrays(nums: &[i64], pattern: &[i64]) -> i64 {
    let n = nums.len();
    let m = pattern.len();

    if m == 0 {
        return n as i64;
    }

    if n <= m {
        return 0;
    }

    let mut lps: Vec<usize> = Vec::new();
    let mut z: usize = 0;
    while z < m {
        lps.push(0);
        z += 1;
    }

    let mut len: usize = 0;
    let mut i: usize = 1;
    while i < m {
        if pattern[i] == pattern[len] {
            len += 1;
            lps[i] = len;
            i += 1;
        } else {
            if len != 0 {
                len = lps[len - 1];
            } else {
                lps[i] = 0;
                i += 1;
            }
        }
    }

    let mut count: i64 = 0;
    let mut j: usize = 0;
    let mut idx: usize = 0;

    while idx + 1 < n {
        let a = nums[idx];
        let b = nums[idx + 1];

        let cur: i64;
        if b > a {
            cur = 1;
        } else if b == a {
            cur = 0;
        } else {
            cur = -1;
        }

        if cur == pattern[j] {
            idx += 1;
            j += 1;

            if j == m {
                count += 1;
                j = lps[j - 1];
            }
        } else {
            if j != 0 {
                j = lps[j - 1];
            } else {
                idx += 1;
            }
        }
    }

    count
}
