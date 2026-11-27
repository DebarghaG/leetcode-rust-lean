fn gcd_i64(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

pub fn max_gcd_sum(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();

    let mut prefix: Vec<i64> = Vec::new();
    prefix.push(0);

    let mut i: usize = 0;
    while i < n {
        let next_sum = prefix[i] + nums[i];
        prefix.push(next_sum);
        i += 1;
    }

    let mut prev_g: Vec<i64> = Vec::new();
    let mut prev_l: Vec<i64> = Vec::new();

    let mut ans: i64 = 0;

    i = 0;
    while i < n {
        let x = nums[i];

        let mut curr_g: Vec<i64> = Vec::new();
        let mut curr_l: Vec<i64> = Vec::new();

        curr_g.push(x);
        curr_l.push(i as i64);

        let mut j: usize = 0;
        while j < prev_g.len() {
            let ng = gcd_i64(prev_g[j], x);
            let nl = prev_l[j];

            let clen = curr_g.len();
            if clen > 0 {
                if curr_g[clen - 1] == ng {
                    let old_l = curr_l[clen - 1];
                    if nl < old_l {
                        curr_l[clen - 1] = nl;
                    }
                } else {
                    curr_g.push(ng);
                    curr_l.push(nl);
                }
            } else {
                curr_g.push(ng);
                curr_l.push(nl);
            }

            j += 1;
        }

        j = 0;
        while j < curr_g.len() {
            let l = curr_l[j];
            let len = (i as i64) - l + 1;

            if len >= k {
                let sum = prefix[i + 1] - prefix[l as usize];
                let value = curr_g[j] * sum;
                if value > ans {
                    ans = value;
                }
            }

            j += 1;
        }

        prev_g = curr_g;
        prev_l = curr_l;

        i += 1;
    }

    ans
}
