pub fn min_cost(nums: &[i64], costs: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut next_ge: Vec<usize> = Vec::new();
    let mut next_less: Vec<usize> = Vec::new();
    let mut i = 0;
    while i < n {
        next_ge.push(n);
        next_less.push(n);
        i += 1;
    }

    // Compute the next index j > i with nums[j] >= nums[i].
    let mut stack_ge: Vec<usize> = Vec::new();
    let mut len_ge: usize = 0;
    let mut j = 0;
    while j < n {
        while len_ge > 0 {
            let top = stack_ge[len_ge - 1];
            if nums[top] <= nums[j] {
                next_ge[top] = j;
                len_ge -= 1;
            } else {
                break;
            }
        }
        if len_ge < stack_ge.len() {
            stack_ge[len_ge] = j;
        } else {
            stack_ge.push(j);
        }
        len_ge += 1;
        j += 1;
    }

    // Compute the next index j > i with nums[j] < nums[i].
    let mut stack_less: Vec<usize> = Vec::new();
    let mut len_less: usize = 0;
    j = 0;
    while j < n {
        while len_less > 0 {
            let top = stack_less[len_less - 1];
            if nums[top] > nums[j] {
                next_less[top] = j;
                len_less -= 1;
            } else {
                break;
            }
        }
        if len_less < stack_less.len() {
            stack_less[len_less] = j;
        } else {
            stack_less.push(j);
        }
        len_less += 1;
        j += 1;
    }

    let inf: i64 = 1_000_000_000_000_000_000;
    let mut dp: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        dp.push(inf);
        i += 1;
    }
    dp[0] = 0;

    i = 0;
    while i < n {
        if dp[i] != inf {
            let t1 = next_ge[i];
            if t1 < n {
                let c1 = dp[i] + costs[t1];
                if c1 < dp[t1] {
                    dp[t1] = c1;
                }
            }

            let t2 = next_less[i];
            if t2 < n {
                let c2 = dp[i] + costs[t2];
                if c2 < dp[t2] {
                    dp[t2] = c2;
                }
            }
        }
        i += 1;
    }

    dp[n - 1]
}
