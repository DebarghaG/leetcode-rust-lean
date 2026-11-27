pub fn maximum_happiness_sum(happiness: &[i64], k: i64) -> i64 {
    let n = happiness.len();

    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(happiness[i]);
        i = i + 1;
    }

    // Iterative bottom-up merge sort, descending.
    let mut width: usize = 1;
    while width < n {
        let mut temp: Vec<i64> = Vec::new();
        let mut left: usize = 0;

        while left < n {
            let mut mid: usize = left + width;
            if mid > n {
                mid = n;
            }

            let mut right: usize = left + 2 * width;
            if right > n {
                right = n;
            }

            let mut a: usize = left;
            let mut b: usize = mid;

            while a < mid && b < right {
                if v[a] >= v[b] {
                    temp.push(v[a]);
                    a = a + 1;
                } else {
                    temp.push(v[b]);
                    b = b + 1;
                }
            }

            while a < mid {
                temp.push(v[a]);
                a = a + 1;
            }

            while b < right {
                temp.push(v[b]);
                b = b + 1;
            }

            left = left + 2 * width;
        }

        v = temp;
        width = width * 2;
    }

    let mut ans: i64 = 0;
    let mut idx: usize = 0;
    let mut dec: i64 = 0;

    while idx < n && dec < k {
        let mut val: i64 = v[idx] - dec;
        if val < 0 {
            val = 0;
        }
        ans = ans + val;
        idx = idx + 1;
        dec = dec + 1;
    }

    ans
}
