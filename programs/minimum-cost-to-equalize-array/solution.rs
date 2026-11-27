fn eval_cost(t: i64, minv: i64, sum: i64, n: i64, cost1: i64, cost2: i64) -> i64 {
    let s = n * t - sum;
    if s <= 0 {
        return 0;
    }

    if cost2 >= cost1 + cost1 {
        return s * cost1;
    }

    let max_def = t - minv;
    let mut pairs = s / 2;

    if max_def + max_def >= s {
        pairs = s - max_def;
    }

    let singles = s - pairs - pairs;
    pairs * cost2 + singles * cost1
}

pub fn min_cost_to_equalize_array(nums: &[i64], cost1: i64, cost2: i64) -> i64 {
    let len = nums.len();
    if len == 0 {
        return 0;
    }

    let mut maxv = nums[0];
    let mut minv = nums[0];
    let mut sum: i64 = 0;
    let mut n: i64 = 0;

    let mut i: usize = 0;
    while i < len {
        let x = nums[i];

        if x > maxv {
            maxv = x;
        }
        if x < minv {
            minv = x;
        }

        sum = sum + x;
        n = n + 1;
        i = i + 1;
    }

    let mut best = eval_cost(maxv, minv, sum, n, cost1, cost2);

    let c = eval_cost(maxv + 1, minv, sum, n, cost1, cost2);
    if c < best {
        best = c;
    }

    if n >= 3 {
        let tbal = (sum - minv - minv) / (n - 2) + 1;

        let tprev = tbal - 1;
        if tprev >= maxv {
            let c0 = eval_cost(tprev, minv, sum, n, cost1, cost2);
            if c0 < best {
                best = c0;
            }
        }

        if tbal >= maxv {
            let c1 = eval_cost(tbal, minv, sum, n, cost1, cost2);
            if c1 < best {
                best = c1;
            }
        }

        let tnext = tbal + 1;
        if tnext >= maxv {
            let c2 = eval_cost(tnext, minv, sum, n, cost1, cost2);
            if c2 < best {
                best = c2;
            }
        }
    }

    best % 1000000007
}
