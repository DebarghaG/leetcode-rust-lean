fn median3(x: i64, y: i64, z: i64) -> i64 {
    if x < y {
        if y < z {
            return y;
        }
        if x < z {
            return z;
        }
        return x;
    } else {
        if x < z {
            return x;
        }
        if y < z {
            return z;
        }
        return y;
    }
}

pub fn largest_even_sum(nums: &[i64], k: i64) -> i64 {
    if k < 0 {
        return -1;
    }
    if k == 0 {
        return 0;
    }

    let n = nums.len();
    let k_usize = k as usize;
    if k_usize > n {
        return -1;
    }

    let mut a: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < n {
        a.push(nums[idx]);
        idx += 1;
    }

    let target: i64 = k - 1;
    let mut left: i64 = 0;
    let mut right: i64 = n as i64 - 1;
    let mut t: i64 = 0;
    let mut found: bool = false;

    while !found && left <= right {
        let mid: i64 = left + (right - left) / 2;
        let p = median3(
            a[left as usize],
            a[mid as usize],
            a[right as usize],
        );

        let mut i: i64 = left;
        let mut lt: i64 = left;
        let mut gt: i64 = right;

        while i <= gt {
            let v = a[i as usize];
            if v > p {
                let tmp = a[lt as usize];
                a[lt as usize] = a[i as usize];
                a[i as usize] = tmp;
                lt += 1;
                i += 1;
            } else if v < p {
                let tmp = a[i as usize];
                a[i as usize] = a[gt as usize];
                a[gt as usize] = tmp;
                gt -= 1;
            } else {
                i += 1;
            }
        }

        if target < lt {
            right = lt - 1;
        } else if target <= gt {
            t = p;
            found = true;
        } else {
            left = gt + 1;
        }
    }

    if !found {
        return -1;
    }

    let mut count_greater: i64 = 0;
    let mut sum_greater: i64 = 0;
    let mut min_greater_odd: i64 = -1;
    let mut min_greater_even: i64 = -1;
    let mut count_equal: i64 = 0;
    let mut max_less_odd: i64 = -1;
    let mut max_less_even: i64 = -1;

    let mut j: usize = 0;
    while j < n {
        let v = nums[j];
        if v > t {
            count_greater += 1;
            sum_greater += v;
            if v % 2 == 0 {
                if min_greater_even == -1 || v < min_greater_even {
                    min_greater_even = v;
                }
            } else {
                if min_greater_odd == -1 || v < min_greater_odd {
                    min_greater_odd = v;
                }
            }
        } else if v == t {
            count_equal += 1;
        } else {
            if v % 2 == 0 {
                if v > max_less_even {
                    max_less_even = v;
                }
            } else {
                if v > max_less_odd {
                    max_less_odd = v;
                }
            }
        }
        j += 1;
    }

    let need: i64 = k - count_greater;
    let leftover: i64 = count_equal - need;
    let sum: i64 = sum_greater + need * t;

    let mut min_selected_odd = min_greater_odd;
    let mut min_selected_even = min_greater_even;

    if need > 0 {
        if t % 2 == 0 {
            min_selected_even = t;
        } else {
            min_selected_odd = t;
        }
    }

    let mut max_unselected_odd = max_less_odd;
    let mut max_unselected_even = max_less_even;

    if leftover > 0 {
        if t % 2 == 0 {
            max_unselected_even = t;
        } else {
            max_unselected_odd = t;
        }
    }

    if sum % 2 == 0 {
        return sum;
    }

    let mut ans: i64 = -1;

    if min_selected_odd != -1 && max_unselected_even != -1 {
        let cand = sum - min_selected_odd + max_unselected_even;
        if cand > ans {
            ans = cand;
        }
    }

    if min_selected_even != -1 && max_unselected_odd != -1 {
        let cand = sum - min_selected_even + max_unselected_odd;
        if cand > ans {
            ans = cand;
        }
    }

    ans
}
