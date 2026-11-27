pub fn valid_substring_count(word1: &[u8], word2: &[u8]) -> i64 {
    let n = word1.len();
    let m = word2.len();

    if m > n {
        return 0;
    }

    let mut need: Vec<i64> = Vec::new();
    let mut have: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < 26 {
        need.push(0);
        have.push(0);
        i += 1;
    }

    let mut missing: i64 = 0;
    i = 0;
    while i < m {
        let idx = (word2[i] - b'a') as usize;
        need[idx] = need[idx] + 1;
        missing = missing + 1;
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut left: usize = 0;
    let mut right: usize = 0;

    while right < n {
        let idx = (word1[right] - b'a') as usize;

        if have[idx] < need[idx] {
            missing = missing - 1;
        }
        have[idx] = have[idx] + 1;

        while missing == 0 {
            ans = ans + (n - right) as i64;

            let left_idx = (word1[left] - b'a') as usize;
            have[left_idx] = have[left_idx] - 1;

            if have[left_idx] < need[left_idx] {
                missing = missing + 1;
            }

            left = left + 1;
        }

        right = right + 1;
    }

    ans
}
