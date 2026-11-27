const MOD: i64 = 1000000007;

fn bit_add(bit: &mut Vec<i64>, n: usize, pos: usize, delta: i64) {
    let mut i = pos + 1;
    while i <= n {
        bit[i] = bit[i] + delta;
        let lsb = i & (!i + 1);
        i += lsb;
    }
}

fn bit_query(bit: &[i64], idx: usize) -> i64 {
    let mut s: i64 = 0;
    let mut i = idx;
    while i > 0 {
        s += bit[i];
        let lsb = i & (!i + 1);
        i -= lsb;
    }
    s
}

pub fn sum_counts(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut maxv: i64 = 0;
    let mut i = 0;
    while i < n {
        if nums[i] > maxv {
            maxv = nums[i];
        }
        i += 1;
    }

    let size = (maxv as usize) + 2;
    let mut last: Vec<i64> = Vec::new();
    i = 0;
    while i < size {
        last.push(-1);
        i += 1;
    }

    let mut bit_cnt: Vec<i64> = Vec::new();
    let mut bit_sum: Vec<i64> = Vec::new();
    i = 0;
    while i <= n {
        bit_cnt.push(0);
        bit_sum.push(0);
        i += 1;
    }

    let mut active_count: i64 = 0;
    let mut total_sum: i64 = 0;
    let mut f: i64 = 0;
    let mut ans: i64 = 0;

    let mut r = 0;
    while r < n {
        let v = nums[r] as usize;
        let p = last[v];

        if p >= 0 {
            let pu = p as usize;
            let less_cnt = bit_query(&bit_cnt, pu);
            let b = bit_query(&bit_sum, pu);
            let g = active_count - less_cnt - 1;

            f = f
                - 2 * b
                - (p + 1) * (2 * g + 1)
                + 2 * (total_sum - (p + 1))
                + (r as i64 + 1);

            bit_add(&mut bit_cnt, n, pu, -1);
            bit_add(&mut bit_sum, n, pu, -(p + 1));
            total_sum = total_sum - (p + 1);
            active_count = active_count - 1;
        } else {
            f = f + 2 * total_sum + (r as i64 + 1);
        }

        bit_add(&mut bit_cnt, n, r, 1);
        bit_add(&mut bit_sum, n, r, r as i64 + 1);
        total_sum = total_sum + (r as i64 + 1);
        active_count = active_count + 1;
        last[v] = r as i64;

        ans = (ans + f % MOD) % MOD;

        r += 1;
    }

    ans
}
