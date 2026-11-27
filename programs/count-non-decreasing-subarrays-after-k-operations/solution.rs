pub fn count_non_decreasing_subarrays(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let size = n + 1;

    // nxt[i] = first index j > i such that nums[j] > nums[i], or n if none.
    let mut nxt: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < size {
        nxt.push(n as i64);
        i += 1;
    }

    let mut stack: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        stack.push(0);
        i += 1;
    }

    let mut sp = 0;
    let mut pos = n;
    while pos > 0 {
        pos -= 1;
        let val = nums[pos];

        while sp > 0 {
            let top = stack[sp - 1] as usize;
            if nums[top] <= val {
                sp -= 1;
            } else {
                break;
            }
        }

        if sp > 0 {
            nxt[pos] = stack[sp - 1];
        } else {
            nxt[pos] = n as i64;
        }

        stack[sp] = pos as i64;
        sp += 1;
    }

    // Prefix sums of nums.
    let mut prefix: Vec<i64> = Vec::new();
    prefix.push(0);
    i = 0;
    while i < n {
        let v = prefix[i] + nums[i];
        prefix.push(v);
        i += 1;
    }

    // Enough binary-lifting levels for chains of next-greater indices.
    let mut levels: usize = 1;
    let mut pwr: i64 = 1;
    while pwr <= (n as i64) + 1 {
        levels += 1;
        pwr *= 2;
    }

    let total = levels * size;
    let mut jump: Vec<i64> = Vec::new();
    let mut sumjump: Vec<i64> = Vec::new();

    i = 0;
    while i < total {
        jump.push(0);
        sumjump.push(0);
        i += 1;
    }

    // Level 0.
    i = 0;
    while i <= n {
        if i < n {
            jump[i] = nxt[i];
            sumjump[i] = nums[i] * (nxt[i] - i as i64);
        } else {
            jump[i] = n as i64;
            sumjump[i] = 0;
        }
        i += 1;
    }

    // Higher levels.
    let mut level = 1;
    while level < levels {
        let prev = (level - 1) * size;
        let base = level * size;

        let mut idx = 0;
        while idx <= n {
            let mid = jump[prev + idx] as usize;
            jump[base + idx] = jump[prev + mid];
            sumjump[base + idx] = sumjump[prev + idx] + sumjump[prev + mid];
            idx += 1;
        }

        level += 1;
    }

    let mut ans: i64 = 0;
    let mut l: usize = 0;
    let mut r: usize = 0;

    while r < n {
        while l <= r {
            let cost = window_cost(l, r, nums, &prefix, &jump, &sumjump, size, levels);
            if cost <= k {
                break;
            }
            l += 1;
        }

        ans += (r as i64) - (l as i64) + 1;
        r += 1;
    }

    ans
}

fn window_cost(
    l: usize,
    r: usize,
    nums: &[i64],
    prefix: &[i64],
    jump: &[i64],
    sumjump: &[i64],
    size: usize,
    levels: usize,
) -> i64 {
    let r_i = r as i64;
    let mut p = l;
    let mut acc: i64 = 0;

    let mut kk = levels;
    while kk > 0 {
        kk -= 1;
        let base = kk * size;
        let q = jump[base + p];

        if q <= r_i {
            acc += sumjump[base + p];
            p = q as usize;
        }
    }

    acc += nums[p] * (r_i + 1 - p as i64);
    acc - (prefix[r + 1] - prefix[l])
}
