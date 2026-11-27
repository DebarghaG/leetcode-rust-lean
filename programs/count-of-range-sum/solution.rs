fn count_leq_bound(arr: &[i64], lo: usize, mid: usize, hi: usize, bound: i64) -> i64 {
    let mut p = lo;
    let mut j = mid;
    let mut total: i64 = 0;

    while j < hi {
        let target = arr[j] - bound;
        while p < mid && arr[p] < target {
            p += 1;
        }
        total += (mid - p) as i64;
        j += 1;
    }

    total
}

fn count_less_bound(arr: &[i64], lo: usize, mid: usize, hi: usize, bound: i64) -> i64 {
    let mut p = lo;
    let mut j = mid;
    let mut total: i64 = 0;

    while j < hi {
        let target = arr[j] - bound;
        while p < mid && arr[p] <= target {
            p += 1;
        }
        total += (mid - p) as i64;
        j += 1;
    }

    total
}

pub fn count_range_sum(nums: &[i64], lower: i64, upper: i64) -> i64 {
    let n = nums.len();
    let m = n + 1;

    let mut vals: Vec<i64> = Vec::new();
    let mut temp: Vec<i64> = Vec::new();

    vals.push(0);
    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        sum += nums[i];
        vals.push(sum);
        i += 1;
    }

    let mut z: usize = 0;
    while z < m {
        temp.push(0);
        z += 1;
    }

    let mut ans: i64 = 0;
    let mut width: usize = 1;

    while width < m {
        let mut lo: usize = 0;

        while lo < m {
            let mid = if lo + width < m { lo + width } else { m };
            let hi = if lo + 2 * width < m { lo + 2 * width } else { m };

            if mid < hi {
                let upper_count = count_leq_bound(&vals, lo, mid, hi, upper);
                let lower_count = count_less_bound(&vals, lo, mid, hi, lower);
                ans += upper_count - lower_count;

                let mut p = lo;
                let mut q = mid;
                let mut k = lo;

                while p < mid && q < hi {
                    if vals[p] <= vals[q] {
                        temp[k] = vals[p];
                        p += 1;
                    } else {
                        temp[k] = vals[q];
                        q += 1;
                    }
                    k += 1;
                }

                while p < mid {
                    temp[k] = vals[p];
                    p += 1;
                    k += 1;
                }

                while q < hi {
                    temp[k] = vals[q];
                    q += 1;
                    k += 1;
                }

                let mut r = lo;
                while r < hi {
                    vals[r] = temp[r];
                    r += 1;
                }
            }

            lo += 2 * width;
        }

        width *= 2;
    }

    ans
}
