const MOD: i64 = 1000000007;

pub fn total_strength(strength: &[i64]) -> i64 {
    let n = strength.len();
    if n == 0 {
        return 0;
    }

    // q[k] = sum_{t = 0}^{k - 1} prefix[t], modulo MOD
    let mut q: Vec<i64> = Vec::new();
    q.push(0);

    let mut pcur: i64 = 0; // prefix sum of strength, modulo MOD
    let mut k: usize = 0;
    while k < n {
        let qprev = q[k];
        q.push((qprev + pcur) % MOD);
        pcur = (pcur + strength[k] % MOD) % MOD;
        k = k + 1;
    }

    let qn = q[n];
    q.push((qn + pcur) % MOD);

    // left[i] = previous index with strictly smaller strength, or -1
    let mut left: Vec<i64> = Vec::new();
    let mut stack: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let ai = strength[i];

        while stack.len() > 0 {
            let top_idx = stack[stack.len() - 1] as usize;
            if strength[top_idx] >= ai {
                stack.pop();
            } else {
                break;
            }
        }

        if stack.len() == 0 {
            left.push(-1);
        } else {
            left.push(stack[stack.len() - 1]);
        }

        stack.push(i as i64);
        i = i + 1;
    }

    let mut ans: i64 = 0;
    let mut stack2: Vec<i64> = Vec::new();

    let mut idx: usize = n;
    while idx > 0 {
        idx = idx - 1;
        let ai = strength[idx];

        // next index with strength <= current strength
        while stack2.len() > 0 {
            let top_idx = stack2[stack2.len() - 1] as usize;
            if strength[top_idx] > ai {
                stack2.pop();
            } else {
                break;
            }
        }

        let right: i64 = if stack2.len() == 0 {
            n as i64
        } else {
            stack2[stack2.len() - 1]
        };

        let l: i64 = left[idx] + 1;
        let r: i64 = right - 1;

        let len_left: i64 = (idx as i64) - l + 1;
        let len_right: i64 = r - (idx as i64) + 1;

        let q_ri = q[(r + 2) as usize];
        let q_ip1 = q[idx + 1];
        let q_l = q[l as usize];

        let mut sum_p1 = q_ri - q_ip1;
        if sum_p1 < 0 {
            sum_p1 = sum_p1 + MOD;
        }

        let mut sum_p2 = q_ip1 - q_l;
        if sum_p2 < 0 {
            sum_p2 = sum_p2 + MOD;
        }

        let term1 = (len_left % MOD) * sum_p1 % MOD;
        let term2 = (len_right % MOD) * sum_p2 % MOD;

        let mut diff = term1 - term2;
        if diff < 0 {
            diff = diff + MOD;
        }

        let ai_mod = ai % MOD;
        let contrib = (ai_mod * diff) % MOD;

        ans = (ans + contrib) % MOD;

        stack2.push(idx as i64);
    }

    ans
}
