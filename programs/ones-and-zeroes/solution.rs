pub fn find_max_form(strs: &[Vec<u8>], m: i64, n: i64) -> i64 {
    let mm = m as usize;
    let nn = n as usize;
    let stride = nn + 1;
    let size = (mm + 1) * stride;

    let mut dp: Vec<i64> = Vec::new();
    let mut idx = 0usize;
    while idx < size {
        dp.push(0);
        idx += 1;
    }

    let mut s_idx = 0usize;
    while s_idx < strs.len() {
        let s = &strs[s_idx];

        let mut zeros = 0usize;
        let mut ones = 0usize;
        let mut b_idx = 0usize;
        while b_idx < s.len() {
            if s[b_idx] == b'0' {
                zeros += 1;
            } else {
                if s[b_idx] == b'1' {
                    ones += 1;
                }
            }
            b_idx += 1;
        }

        if zeros <= mm && ones <= nn {
            let max_i = mm - zeros;
            let max_j = nn - ones;

            let mut i = max_i;
            loop {
                let mut j = max_j;
                loop {
                    let src = i * stride + j;
                    let dst = (i + zeros) * stride + (j + ones);
                    let candidate = dp[src] + 1;
                    if candidate > dp[dst] {
                        dp[dst] = candidate;
                    }

                    if j == 0 {
                        break;
                    }
                    j -= 1;
                }

                if i == 0 {
                    break;
                }
                i -= 1;
            }
        }

        s_idx += 1;
    }

    dp[mm * stride + nn]
}
