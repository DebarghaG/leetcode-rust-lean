fn integer_sqrt(x: i64) -> i64 {
    if x < 2 {
        return x;
    }

    let mut lo: i64 = 1;
    let mut hi: i64 = x;

    while lo <= hi {
        let mid: i64 = lo + (hi - lo) / 2;
        if mid <= x / mid {
            lo = mid + 1;
        } else {
            hi = mid - 1;
        }
    }

    hi
}

pub fn longest_square_streak(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }

    // Bottom-up merge sort of a.
    let mut width: usize = 1;
    while width < n {
        let mut b: Vec<i64> = Vec::new();
        let mut start: usize = 0;

        while start < n {
            let mut mid: usize = start + width;
            if mid > n {
                mid = n;
            }

            let mut end: usize = start + 2 * width;
            if end > n {
                end = n;
            }

            let mut left: usize = start;
            let mut right: usize = mid;

            while left < mid && right < end {
                if a[left] <= a[right] {
                    b.push(a[left]);
                    left += 1;
                } else {
                    b.push(a[right]);
                    right += 1;
                }
            }

            while left < mid {
                b.push(a[left]);
                left += 1;
            }

            while right < end {
                b.push(a[right]);
                right += 1;
            }

            start = end;
        }

        a = b;
        width = width * 2;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut best: i64 = 1;

    i = 0;
    while i < a.len() {
        let x = a[i];
        let root = integer_sqrt(x);
        let mut cur: i64 = 1;

        if root >= 2 && root * root == x {
            let mut lo: usize = 0;
            let mut hi: usize = a.len();
            let mut pos: i64 = -1;

            while lo < hi {
                let mid: usize = lo + (hi - lo) / 2;

                if a[mid] < root {
                    lo = mid + 1;
                } else if a[mid] > root {
                    hi = mid;
                } else {
                    pos = mid as i64;
                    break;
                }
            }

            if pos >= 0 {
                let p: usize = pos as usize;
                if p < dp.len() {
                    cur = dp[p] + 1;
                }
            }
        }

        dp.push(cur);

        if cur > best {
            best = cur;
        }

        i += 1;
    }

    if best >= 2 {
        best
    } else {
        -1
    }
}
