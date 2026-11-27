fn to_digits(mut x: i64) -> Vec<i64> {
    let mut rev: Vec<i64> = Vec::new();
    if x == 0 {
        rev.push(0);
    } else {
        while x > 0 {
            rev.push(x % 10);
            x = x / 10;
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

fn can_one_swap_to(a: &[i64], b: &[i64]) -> bool {
    let n: usize = a.len();
    if b.len() != n {
        return false;
    }

    let mut diff1: usize = n;
    let mut diff2: usize = n;
    let mut mismatches: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        if a[i] != b[i] {
            if mismatches == 0 {
                diff1 = i;
            } else if mismatches == 1 {
                diff2 = i;
            }
            mismatches += 1;
        }
        i += 1;
    }

    if mismatches == 0 {
        return true;
    }

    if mismatches == 2 {
        if diff1 < n && diff2 < n {
            if a[diff1] == b[diff2] && a[diff2] == b[diff1] {
                return true;
            }
        }
    }

    false
}

fn almost_equal_digits(a: &[i64], b: &[i64]) -> bool {
    let la: usize = a.len();
    let lb: usize = b.len();
    let l: usize = if la > lb { la } else { lb };

    if la >= lb {
        let mut target: Vec<i64> = Vec::new();
        let pad: usize = l - lb;
        let mut p: usize = 0;
        while p < pad {
            target.push(0);
            p += 1;
        }
        let mut k: usize = 0;
        while k < lb {
            target.push(b[k]);
            k += 1;
        }
        return can_one_swap_to(a, &target);
    }

    let mut target: Vec<i64> = Vec::new();
    let pad: usize = l - la;
    let mut p: usize = 0;
    while p < pad {
        target.push(0);
        p += 1;
    }
    let mut k: usize = 0;
    while k < la {
        target.push(a[k]);
        k += 1;
    }
    can_one_swap_to(b, &target)
}

pub fn count_pairs(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    let mut count: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let di = to_digits(nums[i]);

        let mut j: usize = i + 1;
        while j < n {
            let dj = to_digits(nums[j]);

            if almost_equal_digits(&di, &dj) {
                count += 1;
            }

            j += 1;
        }

        i += 1;
    }

    count
}
