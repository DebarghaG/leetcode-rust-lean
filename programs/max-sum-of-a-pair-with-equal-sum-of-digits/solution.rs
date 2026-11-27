pub fn maximum_sum(nums: &[i64]) -> i64 {
    let mut best1: Vec<i64> = Vec::new();
    let mut best2: Vec<i64> = Vec::new();

    let mut k: usize = 0;
    while k < 100 {
        best1.push(-1);
        best2.push(-1);
        k += 1;
    }

    let mut i: usize = 0;
    while i < nums.len() {
        let x = nums[i];
        let ds = digit_sum(x) as usize;

        if x > best1[ds] {
            best2[ds] = best1[ds];
            best1[ds] = x;
        } else if x > best2[ds] {
            best2[ds] = x;
        }

        i += 1;
    }

    let mut ans: i64 = -1;
    let mut j: usize = 0;
    while j < 100 {
        if best2[j] >= 0 {
            let cand = best1[j] + best2[j];
            if cand > ans {
                ans = cand;
            }
        }
        j += 1;
    }

    ans
}

fn digit_sum(mut x: i64) -> i64 {
    let mut s: i64 = 0;
    while x > 0 {
        s += x % 10;
        x = x / 10;
    }
    s
}
