pub fn earliest_full_bloom(plantTime: &[i64], growTime: &[i64]) -> i64 {
    let n = plantTime.len();

    let mut order: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        order.push(i as i64);
        i += 1;
    }

    let mut temp: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        temp.push(0);
        i += 1;
    }

    // Sort seed indices by growTime in descending order using iterative merge sort.
    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;

        while left < n {
            let mut mid = left + width;
            if mid > n {
                mid = n;
            }

            let mut right = left + width + width;
            if right > n {
                right = n;
            }

            let mut p: usize = left;
            let mut q: usize = mid;
            let mut k: usize = left;

            while p < mid && q < right {
                let ip = order[p] as usize;
                let iq = order[q] as usize;

                if growTime[ip] >= growTime[iq] {
                    temp[k] = order[p];
                    p += 1;
                } else {
                    temp[k] = order[q];
                    q += 1;
                }

                k += 1;
            }

            while p < mid {
                temp[k] = order[p];
                p += 1;
                k += 1;
            }

            while q < right {
                temp[k] = order[q];
                q += 1;
                k += 1;
            }

            left = right;
        }

        i = 0;
        while i < n {
            order[i] = temp[i];
            i += 1;
        }

        width = width * 2;
    }

    let mut ans: i64 = 0;
    let mut planted: i64 = 0;

    i = 0;
    while i < n {
        let idx = order[i] as usize;
        planted += plantTime[idx];

        let bloom = planted + growTime[idx];
        if bloom > ans {
            ans = bloom;
        }

        i += 1;
    }

    ans
}
