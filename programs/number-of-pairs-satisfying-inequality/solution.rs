pub fn number_of_pairs(nums1: &[i64], nums2: &[i64], diff: i64) -> i64 {
    let n = nums1.len();

    let mut src: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        src.push(nums1[i] - nums2[i]);
        i += 1;
    }

    let mut dst: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        dst.push(0);
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut width: usize = 1;

    while width < n {
        let mut lo: usize = 0;

        while lo < n {
            let mut mid = lo + width;
            if mid > n {
                mid = n;
            }

            let mut hi = lo + width + width;
            if hi > n {
                hi = n;
            }

            let mut p = lo;
            let mut q = mid;
            let mut k = lo;
            let mut p2 = lo;
            let mut cnt: i64 = 0;

            while p < mid && q < hi {
                if src[p] <= src[q] {
                    dst[k] = src[p];
                    p += 1;
                } else {
                    let y = src[q];
                    let limit = y + diff;

                    while p2 < mid && src[p2] <= limit {
                        p2 += 1;
                        cnt += 1;
                    }

                    ans += cnt;
                    dst[k] = y;
                    q += 1;
                }
                k += 1;
            }

            while p < mid {
                dst[k] = src[p];
                p += 1;
                k += 1;
            }

            while q < hi {
                let y = src[q];
                let limit = y + diff;

                while p2 < mid && src[p2] <= limit {
                    p2 += 1;
                    cnt += 1;
                }

                ans += cnt;
                dst[k] = y;
                q += 1;
                k += 1;
            }

            lo = hi;
        }

        let tmp = src;
        src = dst;
        dst = tmp;

        width = width + width;
    }

    ans
}
