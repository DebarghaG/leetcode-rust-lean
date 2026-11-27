pub fn good_days_to_rob_bank(security: &[i64], time: i64) -> Vec<i64> {
    let n: usize = security.len();

    let mut left: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        if i == 0 {
            left.push(0);
        } else if security[i - 1] >= security[i] {
            let prev: i64 = left[i - 1];
            left.push(prev + 1);
        } else {
            left.push(0);
        }
        i += 1;
    }

    let mut rev: Vec<i64> = Vec::new();
    let mut right_run: i64 = 0;
    let mut j: usize = n;

    while j > 0 {
        j -= 1;

        if left[j] >= time && right_run >= time {
            rev.push(j as i64);
        }

        if j > 0 {
            if security[j - 1] <= security[j] {
                right_run = right_run + 1;
            } else {
                right_run = 0;
            }
        }
    }

    let mut out: Vec<i64> = Vec::new();
    let mut k: usize = rev.len();
    while k > 0 {
        k -= 1;
        out.push(rev[k]);
    }

    out
}
