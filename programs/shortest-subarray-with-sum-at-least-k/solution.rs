pub fn shortest_subarray(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();

    let mut prefix: Vec<i64> = Vec::new();
    prefix.push(0);

    let mut i: usize = 0;
    while i < n {
        let s = prefix[i] + nums[i];
        prefix.push(s);
        i += 1;
    }

    let mut dq: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z <= n {
        dq.push(0);
        z += 1;
    }

    let mut head: usize = 0;
    let mut tail: usize = 1;
    dq[0] = 0;

    let mut ans: i64 = n as i64 + 1;
    let mut j: usize = 1;

    while j <= n {
        while head < tail {
            let pos = dq[head] as usize;
            if prefix[j] - prefix[pos] >= k {
                let len: i64 = j as i64 - dq[head];
                if len < ans {
                    ans = len;
                }
                head += 1;
            } else {
                break;
            }
        }

        while head < tail {
            let last_pos = dq[tail - 1] as usize;
            if prefix[last_pos] >= prefix[j] {
                tail -= 1;
            } else {
                break;
            }
        }

        dq[tail] = j as i64;
        tail += 1;
        j += 1;
    }

    if ans == n as i64 + 1 {
        -1
    } else {
        ans
    }
}
