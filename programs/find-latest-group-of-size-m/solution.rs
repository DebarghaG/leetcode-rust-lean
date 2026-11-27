pub fn find_latest_step(arr: &[i64], m: i64) -> i64 {
    let n = arr.len();

    let mut on: Vec<u8> = Vec::new();
    let mut length: Vec<i64> = Vec::new();
    let mut count: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        on.push(0);
        length.push(0);
        i += 1;
    }

    let mut c: usize = 0;
    while c <= n {
        count.push(0);
        c += 1;
    }

    let mut ans: i64 = -1;
    let mut step: usize = 0;

    while step < n {
        let p = (arr[step] - 1) as usize;

        let mut left: i64 = 0;
        if p > 0 {
            if on[p - 1] == 1 {
                left = length[p - 1];
            }
        }

        let mut right: i64 = 0;
        if p + 1 < n {
            if on[p + 1] == 1 {
                right = length[p + 1];
            }
        }

        if left > 0 {
            let li = left as usize;
            count[li] = count[li] - 1;
        }

        if right > 0 {
            let ri = right as usize;
            count[ri] = count[ri] - 1;
        }

        let new_len: i64 = left + right + 1;
        let ni = new_len as usize;
        count[ni] = count[ni] + 1;

        on[p] = 1;
        length[p] = new_len;

        let left_end = (p as i64 - left) as usize;
        let right_end = (p as i64 + right) as usize;
        length[left_end] = new_len;
        length[right_end] = new_len;

        if m >= 1 && m <= n as i64 {
            if count[m as usize] > 0 {
                ans = (step + 1) as i64;
            }
        }

        step += 1;
    }

    ans
}
