pub fn longest_palindrome(word1: &[u8], word2: &[u8]) -> i64 {
    let n1: usize = word1.len();
    let n2: usize = word2.len();
    let n: usize = n1 + n2;

    let mut s: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n1 {
        s.push(word1[i]);
        i += 1;
    }
    i = 0;
    while i < n2 {
        s.push(word2[i]);
        i += 1;
    }

    let total: usize = n * n;
    let mut dp: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < total {
        dp.push(0);
        k += 1;
    }

    i = 0;
    while i < n {
        dp[i * n + i] = 1;
        i += 1;
    }

    let mut length: usize = 2;
    while length <= n {
        let mut left: usize = 0;
        while left + length <= n {
            let right: usize = left + length - 1;
            let idx: usize = left * n + right;

            if s[left] == s[right] {
                if length == 2 {
                    dp[idx] = 2;
                } else {
                    dp[idx] = dp[(left + 1) * n + (right - 1)] + 2;
                }
            } else {
                let a: i64 = dp[(left + 1) * n + right];
                let b: i64 = dp[left * n + (right - 1)];
                if a > b {
                    dp[idx] = a;
                } else {
                    dp[idx] = b;
                }
            }

            left += 1;
        }
        length += 1;
    }

    let mut best: i64 = 0;
    i = 0;
    while i < n1 {
        let mut j: usize = n1;
        while j < n {
            if s[i] == s[j] {
                let value: i64 = dp[i * n + j];
                if value > best {
                    best = value;
                }
            }
            j += 1;
        }
        i += 1;
    }

    best
}
