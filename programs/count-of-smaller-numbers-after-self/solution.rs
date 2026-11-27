pub fn count_smaller(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    let mut result: Vec<i64> = Vec::new();

    if n == 0 {
        return result;
    }

    let mut i: usize = 0;
    while i < n {
        result.push(0);
        i += 1;
    }

    let mut vals: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        vals.push(nums[i]);
        i += 1;
    }

    let mut temp: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        temp.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;
        while left < n {
            let mid: usize;
            if left + width < n {
                mid = left + width;
            } else {
                mid = n;
            }

            let right: usize;
            if mid + width < n {
                right = mid + width;
            } else {
                right = n;
            }

            let mut a = left;
            let mut b = mid;
            let mut k = left;

            while a < mid && b < right {
                if vals[a] <= vals[b] {
                    temp[k] = vals[a];
                    a += 1;
                } else {
                    temp[k] = vals[b];
                    b += 1;
                }
                k += 1;
            }

            while a < mid {
                temp[k] = vals[a];
                a += 1;
                k += 1;
            }

            while b < right {
                temp[k] = vals[b];
                b += 1;
                k += 1;
            }

            left = right;
        }

        i = 0;
        while i < n {
            vals[i] = temp[i];
            i += 1;
        }

        width = width * 2;
    }

    let mut bit: Vec<i64> = Vec::new();
    i = 0;
    while i <= n {
        bit.push(0);
        i += 1;
    }

    let mut idx: usize = n;
    while idx > 0 {
        idx -= 1;
        let x = nums[idx];

        let mut lo: usize = 0;
        let mut hi: usize = n;
        while lo < hi {
            let mid = (lo + hi) / 2;
            if vals[mid] < x {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let rank = lo;

        let mut sum: i64 = 0;
        let mut p = rank;
        while p > 0 {
            sum += bit[p];
            let low = p & (p ^ (p - 1));
            p -= low;
        }

        result[idx] = sum;

        let mut q = rank + 1;
        while q <= n {
            bit[q] += 1;
            let low = q & (q ^ (q - 1));
            q += low;
        }
    }

    result
}
