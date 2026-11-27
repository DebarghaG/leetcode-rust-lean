fn gcd(mut a: i64, mut b: i64) -> i64 {
    if a < 0 {
        a = -a;
    }
    if b < 0 {
        b = -b;
    }
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

fn lcm(a: i64, b: i64) -> i64 {
    if a == 0 || b == 0 {
        return 0;
    }
    let g = gcd(a, b);
    (a / g) * b
}

fn score_without(nums: &[i64], skip: usize) -> i64 {
    let n = nums.len();
    let mut g: i64 = 0;
    let mut l: i64 = 1;
    let mut count: usize = 0;
    let mut i: usize = 0;

    while i < n {
        if i != skip {
            let x = nums[i];
            if count == 0 {
                g = x;
                l = x;
            } else {
                g = gcd(g, x);
                l = lcm(l, x);
            }
            count += 1;
        }
        i += 1;
    }

    if count == 0 {
        0
    } else {
        g * l
    }
}

pub fn max_score(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut best = score_without(nums, n);

    let mut i: usize = 0;
    while i < n {
        let s = score_without(nums, i);
        if s > best {
            best = s;
        }
        i += 1;
    }

    best
}
