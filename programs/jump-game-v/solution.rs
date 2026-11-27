pub fn max_jumps(arr: &[i64], d: i64) -> i64 {
    let n: usize = arr.len();
    if n == 0 {
        return 0;
    }

    let mut order: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        order.push(i);
        i += 1;
    }

    // Insertion-sort indices by arr[index] in nondecreasing order.
    let mut a: usize = 1;
    while a < n {
        let key: usize = order[a];
        let key_val: i64 = arr[key];
        let mut b: usize = a;
        while b > 0 {
            let prev: usize = order[b - 1];
            if arr[prev] <= key_val {
                break;
            }
            order[b] = prev;
            b -= 1;
        }
        order[b] = key;
        a += 1;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < n {
        dp.push(1);
        z += 1;
    }

    let du: usize = d as usize;

    let mut oi: usize = 0;
    while oi < n {
        let idx: usize = order[oi];
        let val: i64 = arr[idx];
        let mut best: i64 = 1;

        let mut step: usize = 1;
        while step <= du {
            if step > idx {
                break;
            }
            let j: usize = idx - step;
            if arr[j] >= val {
                break;
            }
            let cand: i64 = dp[j] + 1;
            if cand > best {
                best = cand;
            }
            step += 1;
        }

        let mut step2: usize = 1;
        while step2 <= du {
            if idx + step2 >= n {
                break;
            }
            let j: usize = idx + step2;
            if arr[j] >= val {
                break;
            }
            let cand: i64 = dp[j] + 1;
            if cand > best {
                best = cand;
            }
            step2 += 1;
        }

        dp[idx] = best;
        oi += 1;
    }

    let mut ans: i64 = 1;
    let mut p: usize = 0;
    while p < n {
        if dp[p] > ans {
            ans = dp[p];
        }
        p += 1;
    }

    ans
}
