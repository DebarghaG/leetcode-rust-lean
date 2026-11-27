fn popcount(mut x: i64) -> usize {
    let mut count: usize = 0;
    while x > 0 {
        if (x & 1) == 1 {
            count += 1;
        }
        x = x >> 1;
    }
    count
}

pub fn count_excellent_pairs(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();

    let mut vals: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        vals.push(nums[i]);
        i += 1;
    }

    // Bottom-up merge sort of vals.
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
            let mut mid = left + width;
            if mid > n {
                mid = n;
            }

            let mut right = left + 2 * width;
            if right > n {
                right = n;
            }

            let mut a = left;
            let mut b = mid;
            let mut out = left;

            while a < mid && b < right {
                if vals[a] <= vals[b] {
                    temp[out] = vals[a];
                    a += 1;
                } else {
                    temp[out] = vals[b];
                    b += 1;
                }
                out += 1;
            }

            while a < mid {
                temp[out] = vals[a];
                a += 1;
                out += 1;
            }

            while b < right {
                temp[out] = vals[b];
                b += 1;
                out += 1;
            }

            left = left + 2 * width;
        }

        let mut p: usize = 0;
        while p < n {
            vals[p] = temp[p];
            p += 1;
        }

        width = width * 2;
    }

    let mut freq: Vec<i64> = Vec::new();
    let mut b: usize = 0;
    while b < 64 {
        freq.push(0);
        b += 1;
    }

    let mut idx: usize = 0;
    while idx < n {
        let v = vals[idx];
        let pc = popcount(v);
        freq[pc] = freq[pc] + 1;

        idx += 1;
        while idx < n && vals[idx] == v {
            idx += 1;
        }
    }

    let mut ans: i64 = 0;
    let mut c: usize = 0;
    while c < 64 {
        let mut d: usize = 0;
        while d < 64 {
            if (c as i64) + (d as i64) >= k {
                ans += freq[c] * freq[d];
            }
            d += 1;
        }
        c += 1;
    }

    ans
}
