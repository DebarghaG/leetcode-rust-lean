pub fn longest_arith_seq_length(nums: &[i64]) -> i64 {
    let n = nums.len();

    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 1;
    }
    if n == 2 {
        return 2;
    }

    let mut minv = nums[0];
    let mut maxv = nums[0];
    let mut i = 1usize;
    while i < n {
        let x = nums[i];
        if x < minv {
            minv = x;
        }
        if x > maxv {
            maxv = x;
        }
        i += 1;
    }

    let span: i64 = maxv - minv;
    let width: usize = (span + 1) as usize;
    let n_i64: i64 = n as i64;

    let mut best: Vec<i64> = Vec::new();
    let mut t = 0usize;
    while t < width {
        best.push(0);
        t += 1;
    }

    let mut ans: i64 = 1;
    let mut d: i64 = -span;

    while d <= span {
        let mut process = true;

        if d != 0 {
            let ad: i64 = if d < 0 { -d } else { d };
            let bound: i64 = span / ad + 1;
            if bound <= ans {
                process = false;
            }
        }

        if process {
            let mut r = 0usize;
            while r < width {
                best[r] = 0;
                r += 1;
            }

            let mut idx = 0usize;
            while idx < n {
                let x = nums[idx];
                let target = x - d;
                let mut cand: i64 = 1;

                if target >= minv && target <= maxv {
                    let tpos: usize = (target - minv) as usize;
                    let prev = best[tpos];
                    cand = prev + 1;
                }

                let xpos: usize = (x - minv) as usize;
                if cand > best[xpos] {
                    best[xpos] = cand;
                }
                if cand > ans {
                    ans = cand;
                }

                idx += 1;
            }
        }

        if ans == n_i64 {
            return ans;
        }

        d += 1;
    }

    ans
}
