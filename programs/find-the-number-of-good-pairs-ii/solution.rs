pub fn number_of_pairs(nums1: &[i64], nums2: &[i64], k: i64) -> i64 {
    let n = nums1.len();

    // We only care about nums1[i] values divisible by k.
    // For those, write nums1[i] = k * q. Then nums2[j] * k divides nums1[i]
    // exactly when nums2[j] divides q.
    let mut max_q: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let v = nums1[i];
        let q = v / k;
        if q * k == v {
            if q > max_q {
                max_q = q;
            }
        }
        i += 1;
    }

    let max_u = max_q as usize;

    let mut count: Vec<i64> = Vec::new();
    let mut x: usize = 0;
    while x <= max_u {
        count.push(0);
        x += 1;
    }

    i = 0;
    while i < n {
        let v = nums1[i];
        let q = v / k;
        if q * k == v {
            let qi = q as usize;
            count[qi] = count[qi] + 1;
        }
        i += 1;
    }

    // Transform count[d] into the number of q-values divisible by d.
    let mut d: usize = 1;
    while d <= max_u {
        let mut total: i64 = 0;
        let mut m: usize = d;
        while m <= max_u {
            total = total + count[m];
            m += d;
        }
        count[d] = total;
        d += 1;
    }

    let mlen = nums2.len();
    let mut ans: i64 = 0;
    let mut j: usize = 0;
    while j < mlen {
        let v = nums2[j];
        if v > 0 && v <= max_q {
            ans = ans + count[v as usize];
        }
        j += 1;
    }

    ans
}
