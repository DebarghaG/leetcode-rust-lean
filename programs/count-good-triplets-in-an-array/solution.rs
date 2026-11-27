fn lowbit(x: usize) -> usize {
    let mut val = x;
    let mut lb: usize = 1;
    while val > 0 && val % 2 == 0 {
        lb *= 2;
        val /= 2;
    }
    lb
}

pub fn good_triplets(nums1: &[i64], nums2: &[i64]) -> i64 {
    let n = nums1.len();

    let mut pos2: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        pos2.push(0);
        i += 1;
    }

    i = 0;
    while i < n {
        let v = nums2[i] as usize;
        pos2[v] = i as i64;
        i += 1;
    }

    let mut a: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        let v = nums1[i] as usize;
        a.push(pos2[v]);
        i += 1;
    }

    let mut left: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        left.push(0);
        i += 1;
    }

    let mut bit: Vec<i64> = Vec::new();
    i = 0;
    while i <= n {
        bit.push(0);
        i += 1;
    }

    i = 0;
    while i < n {
        let v = a[i] as usize;

        let mut idx = v;
        let mut s: i64 = 0;
        while idx > 0 {
            s += bit[idx];
            idx -= lowbit(idx);
        }
        left[i] = s;

        idx = v + 1;
        while idx <= n {
            bit[idx] += 1;
            idx += lowbit(idx);
        }

        i += 1;
    }

    i = 0;
    while i <= n {
        bit[i] = 0;
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut j = n;
    while j > 0 {
        j -= 1;
        let v = a[j] as usize;

        let mut idx = v + 1;
        let mut s: i64 = 0;
        while idx > 0 {
            s += bit[idx];
            idx -= lowbit(idx);
        }

        let seen = (n - 1 - j) as i64;
        let greater = seen - s;
        ans += left[j] * greater;

        idx = v + 1;
        while idx <= n {
            bit[idx] += 1;
            idx += lowbit(idx);
        }
    }

    ans
}
