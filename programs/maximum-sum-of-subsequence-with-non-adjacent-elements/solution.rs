pub fn maximum_sum_subsequence(nums: &[i64], queries: &[Vec<i64>]) -> i64 {
    let mod_val: i64 = 1_000_000_007;
    let neg_inf: i64 = -1_000_000_000_000;

    let n = nums.len();
    let mut size: usize = 1;
    while size < n {
        size = size * 2;
    }

    let total = size * 2;
    let mut m00: Vec<i64> = Vec::new();
    let mut m01: Vec<i64> = Vec::new();
    let mut m10: Vec<i64> = Vec::new();
    let mut m11: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < total {
        m00.push(neg_inf);
        m01.push(neg_inf);
        m10.push(neg_inf);
        m11.push(neg_inf);
        i += 1;
    }

    i = 0;
    while i < size {
        let node = size + i;
        if i < n {
            m00[node] = 0;
            m01[node] = neg_inf;
            m10[node] = neg_inf;
            m11[node] = nums[i];
        } else {
            m00[node] = 0;
            m01[node] = neg_inf;
            m10[node] = neg_inf;
            m11[node] = 0;
        }
        i += 1;
    }

    let mut node: usize = size - 1;
    while node > 0 {
        let l = node * 2;
        let r = l + 1;

        let a00 = m00[l];
        let a01 = m01[l];
        let a10 = m10[l];
        let a11 = m11[l];

        let b00 = m00[r];
        let b01 = m01[r];
        let b10 = m10[r];
        let b11 = m11[r];

        let mut c00 = a00 + b00;
        let mut c01 = a00 + b01;
        let mut c10 = a10 + b00;
        let mut c11 = a10 + b01;

        let t = a00 + b10;
        if t > c00 {
            c00 = t;
        }
        let t = a01 + b00;
        if t > c00 {
            c00 = t;
        }

        let t = a00 + b11;
        if t > c01 {
            c01 = t;
        }
        let t = a01 + b01;
        if t > c01 {
            c01 = t;
        }

        let t = a10 + b10;
        if t > c10 {
            c10 = t;
        }
        let t = a11 + b00;
        if t > c10 {
            c10 = t;
        }

        let t = a10 + b11;
        if t > c11 {
            c11 = t;
        }
        let t = a11 + b01;
        if t > c11 {
            c11 = t;
        }

        m00[node] = c00;
        m01[node] = c01;
        m10[node] = c10;
        m11[node] = c11;

        node -= 1;
    }

    let mut result: i64 = 0;
    let mut qi: usize = 0;

    while qi < queries.len() {
        let pos: usize = queries[qi][0] as usize;
        let x: i64 = queries[qi][1];

        let mut leaf: usize = size + pos;
        m00[leaf] = 0;
        m01[leaf] = neg_inf;
        m10[leaf] = neg_inf;
        m11[leaf] = x;

        leaf = leaf / 2;
        while leaf > 0 {
            let l = leaf * 2;
            let r = l + 1;

            let a00 = m00[l];
            let a01 = m01[l];
            let a10 = m10[l];
            let a11 = m11[l];

            let b00 = m00[r];
            let b01 = m01[r];
            let b10 = m10[r];
            let b11 = m11[r];

            let mut c00 = a00 + b00;
            let mut c01 = a00 + b01;
            let mut c10 = a10 + b00;
            let mut c11 = a10 + b01;

            let t = a00 + b10;
            if t > c00 {
                c00 = t;
            }
            let t = a01 + b00;
            if t > c00 {
                c00 = t;
            }

            let t = a00 + b11;
            if t > c01 {
                c01 = t;
            }
            let t = a01 + b01;
            if t > c01 {
                c01 = t;
            }

            let t = a10 + b10;
            if t > c10 {
                c10 = t;
            }
            let t = a11 + b00;
            if t > c10 {
                c10 = t;
            }

            let t = a10 + b11;
            if t > c11 {
                c11 = t;
            }
            let t = a11 + b01;
            if t > c11 {
                c11 = t;
            }

            m00[leaf] = c00;
            m01[leaf] = c01;
            m10[leaf] = c10;
            m11[leaf] = c11;

            leaf = leaf / 2;
        }

        let mut best = m00[1];
        if m01[1] > best {
            best = m01[1];
        }
        if m10[1] > best {
            best = m10[1];
        }
        if m11[1] > best {
            best = m11[1];
        }

        result = (result + best) % mod_val;
        qi += 1;
    }

    result
}
