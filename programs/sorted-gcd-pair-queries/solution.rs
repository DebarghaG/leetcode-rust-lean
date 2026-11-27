fn gcd_i64(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

fn zeros_i64(len: usize) -> Vec<i64> {
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < len {
        v.push(0);
        i += 1;
    }
    v
}

fn sort_i64(mut v: Vec<i64>) -> Vec<i64> {
    let len = v.len();
    if len < 2 {
        return v;
    }

    let mut tmp: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < len {
        tmp.push(0);
        t += 1;
    }

    let mut width: usize = 1;
    while width < len {
        let mut left: usize = 0;
        while left < len {
            let mut mid = left + width;
            if mid > len {
                mid = len;
            }
            let mut right = mid + width;
            if right > len {
                right = len;
            }

            let mut i = left;
            let mut j = mid;
            let mut k = left;

            while i < mid && j < right {
                if v[i] <= v[j] {
                    tmp[k] = v[i];
                    i += 1;
                } else {
                    tmp[k] = v[j];
                    j += 1;
                }
                k += 1;
            }

            while i < mid {
                tmp[k] = v[i];
                i += 1;
                k += 1;
            }

            while j < right {
                tmp[k] = v[j];
                j += 1;
                k += 1;
            }

            left = right;
        }

        let mut p: usize = 0;
        while p < len {
            v[p] = tmp[p];
            p += 1;
        }

        width = width * 2;
    }

    v
}

pub fn gcd_values(nums: &[i64], queries: &[i64]) -> Vec<i64> {
    let n: usize = nums.len();
    let n_i: i64 = n as i64;
    let total_pairs: i64 = n_i * (n_i - 1) / 2;

    let mut max_orig: i64 = nums[0];
    let mut i: usize = 1;
    while i < n {
        if nums[i] > max_orig {
            max_orig = nums[i];
        }
        i += 1;
    }

    if total_pairs <= 20000 {
        let mut pairs: Vec<i64> = Vec::new();

        let mut a: usize = 0;
        while a < n {
            let mut b: usize = a + 1;
            while b < n {
                pairs.push(gcd_i64(nums[a], nums[b]));
                b += 1;
            }
            a += 1;
        }

        pairs = sort_i64(pairs);

        let mut ans: Vec<i64> = Vec::new();
        let mut qi: usize = 0;
        while qi < queries.len() {
            let q = queries[qi];
            if q < 0 || q >= total_pairs {
                ans.push(max_orig + 1);
            } else {
                let idx = q as usize;
                ans.push(pairs[idx]);
            }
            qi += 1;
        }

        return ans;
    }

    let mut g: i64 = nums[0];
    let mut gi: usize = 1;
    while gi < n {
        g = gcd_i64(g, nums[gi]);
        gi += 1;
    }

    let m_i: i64 = max_orig / g;
    let m: usize = m_i as usize;

    let mut freq: Vec<i64> = zeros_i64(m + 1);
    let mut fi: usize = 0;
    while fi < n {
        let val = nums[fi] / g;
        let idx = val as usize;
        freq[idx] += 1;
        fi += 1;
    }

    let mut exact: Vec<i64> = zeros_i64(m + 1);

    let mut d: usize = m;
    while d > 0 {
        let mut c: i64 = freq[d];
        let mut sub: i64 = 0;

        let mut mk: usize = d + d;
        while mk <= m {
            c += freq[mk];
            sub += exact[mk];
            mk += d;
        }

        exact[d] = c * (c - 1) / 2 - sub;
        d -= 1;
    }

    let mut running: i64 = 0;
    let mut d2: usize = 1;
    while d2 <= m {
        running += exact[d2];
        exact[d2] = running;
        d2 += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut qi: usize = 0;
    while qi < queries.len() {
        let q = queries[qi];

        if q < 0 || q >= total_pairs {
            ans.push(max_orig + 1);
        } else {
            let target: i64 = q + 1;
            let mut left: usize = 1;
            let mut right: usize = m;

            while left < right {
                let mid: usize = left + (right - left) / 2;
                if exact[mid] >= target {
                    right = mid;
                } else {
                    left = mid + 1;
                }
            }

            ans.push((left as i64) * g);
        }

        qi += 1;
    }

    ans
}
