pub fn max_score(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut minv: i64 = nums[0];
    let mut maxv: i64 = nums[0];

    let mut i: usize = 1;
    while i < n {
        let x = nums[i];
        if x < minv {
            minv = x;
        }
        if x > maxv {
            maxv = x;
        }
        i += 1;
    }

    let span: i64 = maxv - minv + 1;
    let mut counts: Vec<i64> = Vec::new();
    let mut k: i64 = 0;
    while k < span {
        counts.push(0);
        k += 1;
    }

    let mut j: usize = 0;
    while j < n {
        let x = nums[j];
        let idx = (x - minv) as usize;
        counts[idx] = counts[idx] + 1;
        j += 1;
    }

    let mut sum: i64 = 0;
    let mut score: i64 = 0;
    let mut v: i64 = maxv;

    while v >= minv {
        let idx = (v - minv) as usize;
        let mut c: i64 = counts[idx];

        while c > 0 {
            sum = sum + v;
            if sum > 0 {
                score = score + 1;
            }
            c -= 1;
        }

        v -= 1;
    }

    score
}
