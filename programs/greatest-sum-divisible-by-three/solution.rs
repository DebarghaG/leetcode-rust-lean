pub fn max_sum_div_three(nums: &[i64]) -> i64 {
    let mut d0: i64 = 0;
    let mut d1: i64 = -1;
    let mut d2: i64 = -1;

    let mut i: usize = 0;
    while i < nums.len() {
        let x = nums[i];
        let mut r = x % 3;
        if r < 0 {
            r = r + 3;
        }

        let mut n0 = d0;
        let mut n1 = d1;
        let mut n2 = d2;

        if d0 >= 0 {
            let c = d0 + x;
            let ns = r;
            if ns == 0 {
                if c > n0 {
                    n0 = c;
                }
            } else if ns == 1 {
                if c > n1 {
                    n1 = c;
                }
            } else {
                if c > n2 {
                    n2 = c;
                }
            }
        }

        if d1 >= 0 {
            let c = d1 + x;
            let ns = (1 + r) % 3;
            if ns == 0 {
                if c > n0 {
                    n0 = c;
                }
            } else if ns == 1 {
                if c > n1 {
                    n1 = c;
                }
            } else {
                if c > n2 {
                    n2 = c;
                }
            }
        }

        if d2 >= 0 {
            let c = d2 + x;
            let ns = (2 + r) % 3;
            if ns == 0 {
                if c > n0 {
                    n0 = c;
                }
            } else if ns == 1 {
                if c > n1 {
                    n1 = c;
                }
            } else {
                if c > n2 {
                    n2 = c;
                }
            }
        }

        d0 = n0;
        d1 = n1;
        d2 = n2;

        i += 1;
    }

    d0
}
