pub fn modified_list(nums: &[i64], head: &List) -> List {
    let mut sorted: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < nums.len() {
        sorted.push(nums[idx]);
        idx += 1;
    }

    let n: usize = sorted.len();

    if n > 1 {
        let mut tmp: Vec<i64> = Vec::new();
        let mut t: usize = 0;
        while t < n {
            tmp.push(0);
            t += 1;
        }

        let mut width: usize = 1;
        while width < n {
            let width2: usize = width + width;
            let mut start: usize = 0;

            while start < n {
                let mut mid: usize = start + width;
                if mid > n {
                    mid = n;
                }

                let mut end: usize = start + width2;
                if end > n {
                    end = n;
                }

                let mut i: usize = start;
                let mut j: usize = mid;
                let mut k: usize = start;

                while i < mid && j < end {
                    if sorted[i] <= sorted[j] {
                        tmp[k] = sorted[i];
                        i += 1;
                    } else {
                        tmp[k] = sorted[j];
                        j += 1;
                    }
                    k += 1;
                }

                while i < mid {
                    tmp[k] = sorted[i];
                    i += 1;
                    k += 1;
                }

                while j < end {
                    tmp[k] = sorted[j];
                    j += 1;
                    k += 1;
                }

                start = end;
            }

            let mut p: usize = 0;
            while p < n {
                sorted[p] = tmp[p];
                p += 1;
            }

            width = width2;
        }
    }

    let mut kept: Vec<i64> = Vec::new();
    let mut cur: &List = head;
    let mut done: bool = false;

    while !done {
        match cur {
            List::Nil => {
                done = true;
            }
            List::Cons(v, next) => {
                let val: i64 = *v;
                if !contains_sorted(&sorted, val) {
                    kept.push(val);
                }
                cur = &**next;
            }
        }
    }

    let mut result: List = List::Nil;
    let mut k: usize = kept.len();
    while k > 0 {
        k -= 1;
        let val: i64 = kept[k];
        result = List::Cons(val, Box::new(result));
    }

    result
}

fn contains_sorted(xs: &[i64], val: i64) -> bool {
    let mut lo: usize = 0;
    let mut hi: usize = xs.len();

    while lo < hi {
        let mid: usize = lo + (hi - lo) / 2;

        if xs[mid] == val {
            return true;
        } else if xs[mid] < val {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    false
}
