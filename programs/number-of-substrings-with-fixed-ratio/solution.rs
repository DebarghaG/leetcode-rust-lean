pub fn fixed_ratio(s: &[u8], num1: i64, num2: i64) -> i64 {
    let n: usize = s.len();
    let len: usize = n + 1;

    // prefix value = num2 * (#zeros) - num1 * (#ones)
    // Two prefix positions form a valid substring exactly when their values are equal.
    let mut vals: Vec<i64> = Vec::new();
    let mut prefix: i64 = 0;
    vals.push(prefix);

    let mut i: usize = 0;
    while i < n {
        if s[i] == b'0' {
            prefix = prefix + num2;
        } else {
            prefix = prefix - num1;
        }
        vals.push(prefix);
        i += 1;
    }

    // Bottom-up merge sort, avoiding recursion and standard-library sorting.
    let mut temp: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < len {
        temp.push(0);
        j += 1;
    }

    let mut width: usize = 1;
    while width < len {
        let mut left: usize = 0;
        while left < len {
            let mut mid: usize = left + width;
            if mid > len {
                mid = len;
            }

            let mut right: usize = left + width * 2;
            if right > len {
                right = len;
            }

            let mut a: usize = left;
            let mut b: usize = mid;
            let mut k: usize = left;

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

            left = left + width * 2;
        }

        let mut t: usize = 0;
        while t < len {
            vals[t] = temp[t];
            t += 1;
        }

        width = width * 2;
    }

    // Count pairs of equal prefix values.
    let mut ans: i64 = 0;
    let mut i2: usize = 0;
    while i2 < len {
        let mut j2: usize = i2 + 1;
        while j2 < len && vals[j2] == vals[i2] {
            j2 += 1;
        }

        let count: i64 = (j2 - i2) as i64;
        ans = ans + count * (count - 1) / 2;
        i2 = j2;
    }

    ans
}
