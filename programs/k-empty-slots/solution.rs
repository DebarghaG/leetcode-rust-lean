pub fn k_empty_slots(bulbs: &[i64], k: i64) -> i64 {
    let n = bulbs.len();
    if n == 0 {
        return -1;
    }
    if k < 0 {
        return -1;
    }
    let kk = k as usize;
    if kk + 2 > n {
        return -1;
    }

    let mut days: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        days.push(0);
        i += 1;
    }

    i = 0;
    while i < n {
        let pos = bulbs[i] as usize;
        days[pos - 1] = (i as i64) + 1;
        i += 1;
    }

    let last_l = n - kk - 2;
    let mut ans = (n as i64) + 1;

    if kk == 0 {
        let mut l: usize = 0;
        while l <= last_l {
            let a = days[l];
            let b = days[l + 1];
            let mut mx = a;
            if b > mx {
                mx = b;
            }
            if mx < ans {
                ans = mx;
            }
            l += 1;
        }
        if ans <= n as i64 {
            return ans;
        } else {
            return -1;
        }
    }

    let mut q: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        q.push(0);
        i += 1;
    }

    let mut head: usize = 0;
    let mut tail: usize = 0;

    let mut idx: usize = 1;
    while idx <= kk {
        let val = days[idx];
        while tail > head {
            let last = q[tail - 1] as usize;
            if days[last] >= val {
                tail -= 1;
            } else {
                break;
            }
        }
        q[tail] = idx as i64;
        tail += 1;
        idx += 1;
    }

    let mut l: usize = 0;
    while l <= last_l {
        let min_mid = days[q[head] as usize];
        let a = days[l];
        let b = days[l + kk + 1];

        let mut mx = a;
        if b > mx {
            mx = b;
        }

        if mx < min_mid && mx < ans {
            ans = mx;
        }

        if l < last_l {
            if head < tail && q[head] as usize == l + 1 {
                head += 1;
            }

            let new_idx = l + kk + 1;
            let val = days[new_idx];

            while tail > head {
                let last = q[tail - 1] as usize;
                if days[last] >= val {
                    tail -= 1;
                } else {
                    break;
                }
            }

            q[tail] = new_idx as i64;
            tail += 1;
        }

        l += 1;
    }

    if ans <= n as i64 {
        ans
    } else {
        -1
    }
}
