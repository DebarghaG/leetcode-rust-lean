fn min_usize(a: usize, b: usize) -> usize {
    if a < b {
        a
    } else {
        b
    }
}

fn sorted_copy(xs: &[i64]) -> Vec<i64> {
    let n = xs.len();
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        a.push(xs[i]);
        i += 1;
    }

    if n <= 1 {
        return a;
    }

    let mut tmp: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        tmp.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;
        while left < n {
            let mid = min_usize(left + width, n);
            let right = min_usize(left + width + width, n);

            let mut p: usize = left;
            let mut q: usize = mid;
            let mut k: usize = left;

            while p < mid && q < right {
                if a[p] <= a[q] {
                    tmp[k] = a[p];
                    p += 1;
                } else {
                    tmp[k] = a[q];
                    q += 1;
                }
                k += 1;
            }

            while p < mid {
                tmp[k] = a[p];
                p += 1;
                k += 1;
            }

            while q < right {
                tmp[k] = a[q];
                q += 1;
                k += 1;
            }

            left = right;
        }

        let mut j: usize = 0;
        while j < n {
            a[j] = tmp[j];
            j += 1;
        }

        width = width + width;
    }

    a
}

pub fn minimum_time(jobs: &[i64], workers: &[i64]) -> i64 {
    let n = jobs.len();
    let sorted_jobs = sorted_copy(jobs);
    let sorted_workers = sorted_copy(workers);

    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let job = sorted_jobs[i];
        let worker = sorted_workers[i];

        let mut days = job / worker;
        if job % worker != 0 {
            days = days + 1;
        }

        if days > ans {
            ans = days;
        }

        i += 1;
    }

    ans
}
