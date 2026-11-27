fn lower_bound_pos(ps: &[i64], target: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = ps.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if ps[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

fn upper_bound_pos(ps: &[i64], target: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = ps.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if ps[mid] <= target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

pub fn minimum_moves(nums: &[i64], k: i64, maxChanges: i64) -> i64 {
    let n = nums.len();
    let mut pos: Vec<i64> = Vec::new();

    let mut idx: usize = 0;
    while idx < n {
        if nums[idx] == 1 {
            pos.push(idx as i64);
        }
        idx += 1;
    }

    let m = pos.len();

    if m == 0 {
        return 2 * k;
    }

    let mut pref: Vec<i64> = Vec::new();
    pref.push(0);

    let mut j: usize = 0;
    while j < m {
        let value = pref[j] + pos[j];
        pref.push(value);
        j += 1;
    }

    let mut ans: i64 = 1000000000000000000;
    let mut i: usize = 0;

    while i < m {
        let center = pos[i];

        let mut cnt1: i64 = 0;
        if i > 0 {
            if pos[i - 1] + 1 == center {
                cnt1 += 1;
            }
        }
        if i + 1 < m {
            if pos[i + 1] - 1 == center {
                cnt1 += 1;
            }
        }

        let mut cost: i64 = 0;
        let rem = k - 1;

        if rem > 0 {
            let use1 = if rem < cnt1 { rem } else { cnt1 };
            cost = use1;

            let rem2 = rem - use1;

            if rem2 > 0 {
                if rem2 <= maxChanges {
                    cost = cost + 2 * rem2;
                } else {
                    let t = rem2 - maxChanges;
                    let base = cost + 2 * maxChanges;

                    let hi0 = pos[m - 1] - pos[0] + 2;
                    let mut lo: i64 = 2;
                    let mut hi: i64 = hi0;

                    while lo < hi {
                        let mid = lo + (hi - lo) / 2;
                        let l = lower_bound_pos(&pos, center - mid);
                        let r = upper_bound_pos(&pos, center + mid);
                        let far_count = (r as i64 - l as i64) - 1 - cnt1;

                        if far_count >= t {
                            hi = mid;
                        } else {
                            lo = mid + 1;
                        }
                    }

                    let radius = lo;
                    let rad = radius - 1;

                    let l = lower_bound_pos(&pos, center - rad);
                    let r = upper_bound_pos(&pos, center + rad);

                    let mut total_dist: i64 = 0;

                    if l < i {
                        let left_count = (i - l) as i64;
                        let left_sum = pref[i] - pref[l];
                        total_dist = total_dist + center * left_count - left_sum;
                    }

                    if r > i + 1 {
                        let right_count = (r - (i + 1)) as i64;
                        let right_sum = pref[r] - pref[i + 1];
                        total_dist = total_dist + right_sum - center * right_count;
                    }

                    let total_count: i64 = r as i64 - l as i64 - 1;
                    let far_count_less = total_count - cnt1;
                    let far_sum_less = total_dist - cnt1;
                    let need_now = t - far_count_less;

                    cost = base + far_sum_less + need_now * radius;
                }
            }
        }

        if cost < ans {
            ans = cost;
        }

        i += 1;
    }

    ans
}
