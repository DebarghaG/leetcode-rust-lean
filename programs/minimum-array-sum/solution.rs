pub fn min_array_sum(nums: &[i64], k: i64, op1: i64, op2: i64) -> i64 {
    let n = nums.len();
    let n1 = op1 as usize;
    let n2 = op2 as usize;

    let rows = n1 + 1;
    let cols = n2 + 1;
    let size = rows * cols;

    let inf: i64 = 1000000000000000000;

    let mut dp: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < size {
        dp.push(inf);
        i += 1;
    }
    dp[0] = 0;

    let mut pos_nums = 0;
    while pos_nums < n {
        let x = nums[pos_nums];

        let mut ndp: Vec<i64> = Vec::new();
        i = 0;
        while i < size {
            ndp.push(inf);
            i += 1;
        }

        let mut a = 0;
        while a < rows {
            let mut b = 0;
            while b < cols {
                let pos = a * cols + b;
                let cur = dp[pos];

                if cur != inf {
                    if cur + x < ndp[pos] {
                        ndp[pos] = cur + x;
                    }

                    if a < n1 {
                        let y = (x + 1) / 2;
                        let pos1 = (a + 1) * cols + b;
                        if cur + y < ndp[pos1] {
                            ndp[pos1] = cur + y;
                        }
                    }

                    if b < n2 && x >= k {
                        let y = x - k;
                        let pos2 = a * cols + (b + 1);
                        if cur + y < ndp[pos2] {
                            ndp[pos2] = cur + y;
                        }
                    }

                    if a < n1 && b < n2 {
                        let mut best = inf;

                        let y1 = (x + 1) / 2;
                        if y1 >= k {
                            let v = y1 - k;
                            if v < best {
                                best = v;
                            }
                        }

                        if x >= k {
                            let y2 = x - k;
                            let v = (y2 + 1) / 2;
                            if v < best {
                                best = v;
                            }
                        }

                        if best != inf {
                            let pos12 = (a + 1) * cols + (b + 1);
                            if cur + best < ndp[pos12] {
                                ndp[pos12] = cur + best;
                            }
                        }
                    }
                }

                b += 1;
            }
            a += 1;
        }

        dp = ndp;
        pos_nums += 1;
    }

    let mut ans = inf;
    i = 0;
    while i < size {
        if dp[i] < ans {
            ans = dp[i];
        }
        i += 1;
    }

    ans
}
