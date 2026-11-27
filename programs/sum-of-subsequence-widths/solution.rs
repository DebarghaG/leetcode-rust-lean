pub fn sum_subseq_widths(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n <= 1 {
        return 0;
    }

    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }

    // Build a max-heap.
    let mut start: usize = n / 2;
    while start > 0 {
        start -= 1;

        let mut root: usize = start;
        let mut going: bool = true;
        while going {
            let child_base: usize = root * 2 + 1;
            if child_base >= n {
                going = false;
            } else {
                let mut child: usize = child_base;
                if child + 1 < n {
                    if a[child] < a[child + 1] {
                        child += 1;
                    }
                }

                if a[root] < a[child] {
                    let tmp = a[root];
                    a[root] = a[child];
                    a[child] = tmp;
                    root = child;
                } else {
                    going = false;
                }
            }
        }
    }

    // Extract elements from the max-heap, producing sorted ascending order.
    let mut end: usize = n;
    while end > 1 {
        end -= 1;

        let tmp = a[0];
        a[0] = a[end];
        a[end] = tmp;

        let mut root: usize = 0;
        let mut going: bool = true;
        while going {
            let child_base: usize = root * 2 + 1;
            if child_base >= end {
                going = false;
            } else {
                let mut child: usize = child_base;
                if child + 1 < end {
                    if a[child] < a[child + 1] {
                        child += 1;
                    }
                }

                if a[root] < a[child] {
                    let tmp2 = a[root];
                    a[root] = a[child];
                    a[child] = tmp2;
                    root = child;
                } else {
                    going = false;
                }
            }
        }
    }

    let modulus: i64 = 1_000_000_007;

    // Sum of subsequence maximums:
    // sum a[i] * 2^i for sorted a.
    let mut sum1: i64 = 0;
    let mut p: i64 = 1;
    i = 0;
    while i < n {
        let term = ((a[i] % modulus) * p) % modulus;
        sum1 = (sum1 + term) % modulus;
        p = (p * 2) % modulus;
        i += 1;
    }

    // Sum of subsequence minimums:
    // sum a[i] * 2^(n-1-i) for sorted a.
    let mut sum2: i64 = 0;
    p = 1;
    i = n;
    while i > 0 {
        i -= 1;
        let term = ((a[i] % modulus) * p) % modulus;
        sum2 = (sum2 + term) % modulus;
        p = (p * 2) % modulus;
    }

    let mut ans = sum1 - sum2;
    if ans < 0 {
        ans += modulus;
    }
    ans
}
