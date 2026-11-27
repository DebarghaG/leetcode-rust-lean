fn count_leq(x: i64, limit: i64, ch0: &[i64], ch1: &[i64], cnt: &[i64]) -> i64 {
    if limit < 0 {
        return 0;
    }

    let max_bit: i64 = 15;
    let mut cur: i64 = 0;
    let mut ans: i64 = 0;
    let mut bit: i64 = max_bit;

    while bit >= 0 {
        if cur == -1 {
            return ans;
        }

        let ci = cur as usize;
        let xb = (x >> bit) & 1;
        let lb = (limit >> bit) & 1;

        if xb == 0 {
            if lb == 1 {
                let c0 = ch0[ci];
                if c0 != -1 {
                    ans = ans + cnt[c0 as usize];
                }
                cur = ch1[ci];
            } else {
                cur = ch0[ci];
            }
        } else {
            if lb == 1 {
                let c1 = ch1[ci];
                if c1 != -1 {
                    ans = ans + cnt[c1 as usize];
                }
                cur = ch0[ci];
            } else {
                cur = ch1[ci];
            }
        }

        bit = bit - 1;
    }

    if cur != -1 {
        ans = ans + cnt[cur as usize];
    }

    ans
}

pub fn count_pairs(nums: &[i64], low: i64, high: i64) -> i64 {
    let max_bit: i64 = 15;

    let mut ch0: Vec<i64> = Vec::new();
    let mut ch1: Vec<i64> = Vec::new();
    let mut cnt: Vec<i64> = Vec::new();

    ch0.push(-1);
    ch1.push(-1);
    cnt.push(0);

    let mut ans: i64 = 0;
    let n = nums.len();
    let mut i: usize = 0;

    while i < n {
        let x = nums[i];

        let high_count = count_leq(x, high, &ch0[..], &ch1[..], &cnt[..]);
        let low_count = count_leq(x, low - 1, &ch0[..], &ch1[..], &cnt[..]);
        ans = ans + high_count - low_count;

        let mut cur: i64 = 0;
        let root_idx = cur as usize;
        cnt[root_idx] = cnt[root_idx] + 1;

        let mut bit: i64 = max_bit;
        while bit >= 0 {
            let ci = cur as usize;
            let b = (x >> bit) & 1;

            if b == 0 {
                let mut nxt = ch0[ci];
                if nxt == -1 {
                    nxt = ch0.len() as i64;
                    ch0[ci] = nxt;
                    ch0.push(-1);
                    ch1.push(-1);
                    cnt.push(0);
                }
                cur = nxt;
            } else {
                let mut nxt = ch1[ci];
                if nxt == -1 {
                    nxt = ch1.len() as i64;
                    ch1[ci] = nxt;
                    ch0.push(-1);
                    ch1.push(-1);
                    cnt.push(0);
                }
                cur = nxt;
            }

            let cj = cur as usize;
            cnt[cj] = cnt[cj] + 1;

            bit = bit - 1;
        }

        i = i + 1;
    }

    ans
}
