pub fn len_longest_fib_subseq(arr: &[i64]) -> i64 {
    let n = arr.len();
    if n < 3 {
        return 0;
    }

    let total = n * n;
    let mut dp: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < total {
        dp.push(0);
        t += 1;
    }

    let mut ans: i64 = 0;
    let mut i: usize = 1;

    while i < n {
        let mut j: usize = 0;

        while j < i {
            let target = arr[i] - arr[j];

            let mut lo: usize = 0;
            let mut hi: usize = j;
            let mut found: usize = j;

            while lo < hi {
                let mid = (lo + hi) / 2;
                if arr[mid] == target {
                    found = mid;
                    lo = hi;
                } else if arr[mid] < target {
                    lo = mid + 1;
                } else {
                    hi = mid;
                }
            }

            let mut len: i64 = 2;

            if found < j {
                let prev = dp[found * n + j];
                if prev >= 2 {
                    len = prev + 1;
                }
            }

            dp[j * n + i] = len;

            if len > ans {
                ans = len;
            }

            j += 1;
        }

        i += 1;
    }

    if ans < 3 {
        0
    } else {
        ans
    }
}
