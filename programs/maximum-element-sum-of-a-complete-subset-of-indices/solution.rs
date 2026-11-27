fn squarefree_kernel(mut x: usize) -> usize {
    let mut d: usize = 2;
    while d * d <= x {
        let sq = d * d;
        while x % sq == 0 {
            x = x / sq;
        }
        d += 1;
    }
    x
}

pub fn maximum_sum(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut sums: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= n {
        sums.push(0);
        i += 1;
    }

    i = 1;
    while i <= n {
        let k = squarefree_kernel(i);
        sums[k] += nums[i - 1];
        i += 1;
    }

    let mut ans: i64 = 0;
    i = 1;
    while i <= n {
        if sums[i] > ans {
            ans = sums[i];
        }
        i += 1;
    }

    ans
}
