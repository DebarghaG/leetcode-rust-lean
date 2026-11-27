pub fn longest_subarray(nums: &[i64], limit: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut maxq: Vec<i64> = Vec::new();
    let mut minq: Vec<i64> = Vec::new();

    let mut init: usize = 0;
    while init < n {
        maxq.push(0);
        minq.push(0);
        init += 1;
    }

    let mut hmax: usize = 0;
    let mut tmax: usize = 0;
    let mut hmin: usize = 0;
    let mut tmin: usize = 0;

    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut ans: i64 = 0;

    while right < n {
        let x = nums[right];

        while tmax > hmax {
            let idx = maxq[tmax - 1] as usize;
            if nums[idx] <= x {
                tmax -= 1;
            } else {
                break;
            }
        }
        maxq[tmax] = right as i64;
        tmax += 1;

        while tmin > hmin {
            let idx = minq[tmin - 1] as usize;
            if nums[idx] >= x {
                tmin -= 1;
            } else {
                break;
            }
        }
        minq[tmin] = right as i64;
        tmin += 1;

        while hmax < tmax && hmin < tmin {
            let mx = nums[maxq[hmax] as usize];
            let mn = nums[minq[hmin] as usize];

            if mx - mn <= limit {
                break;
            }

            if maxq[hmax] as usize == left {
                hmax += 1;
            }
            if minq[hmin] as usize == left {
                hmin += 1;
            }
            left += 1;
        }

        let cur = (right - left + 1) as i64;
        if cur > ans {
            ans = cur;
        }

        right += 1;
    }

    ans
}
