pub fn delete_duplicates_unsorted(head: &List) -> List {
    // Collect all values in the original order.
    let mut vals: Vec<i64> = Vec::new();
    let mut cur: &List = head;
    let mut running: bool = true;

    while running {
        match cur {
            List::Nil => {
                running = false;
            }
            List::Cons(v, next) => {
                vals.push(*v);
                cur = &**next;
            }
        }
    }

    let n: usize = vals.len();
    if n == 0 {
        return List::Nil;
    }

    // Make a sorted copy of vals using bottom-up merge sort.
    let mut sorted: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        sorted.push(vals[i]);
        i += 1;
    }

    let mut aux: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        aux.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut start: usize = 0;
        while start < n {
            let mid = if start + width < n { start + width } else { n };
            let end = if start + width + width < n {
                start + width + width
            } else {
                n
            };

            let mut a: usize = start;
            let mut b: usize = mid;
            let mut k: usize = start;

            while a < mid && b < end {
                if sorted[a] <= sorted[b] {
                    aux[k] = sorted[a];
                    a += 1;
                } else {
                    aux[k] = sorted[b];
                    b += 1;
                }
                k += 1;
            }

            while a < mid {
                aux[k] = sorted[a];
                a += 1;
                k += 1;
            }

            while b < end {
                aux[k] = sorted[b];
                b += 1;
                k += 1;
            }

            start = end;
        }

        let mut p: usize = 0;
        while p < n {
            sorted[p] = aux[p];
            p += 1;
        }

        width = width + width;
    }

    // Keep exactly the values whose total frequency in sorted is one.
    let mut keep: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        let x: i64 = vals[i];

        // First position of x.
        let mut lo: usize = 0;
        let mut hi: usize = n;
        while lo < hi {
            let mid = (lo + hi) / 2;
            if sorted[mid] < x {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let first = lo;

        // First position strictly greater than x.
        lo = 0;
        hi = n;
        while lo < hi {
            let mid = (lo + hi) / 2;
            if sorted[mid] <= x {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let last = lo;

        if last - first == 1 {
            keep.push(x);
        }

        i += 1;
    }

    // Build the resulting linked list from the tail up.
    let mut out: List = List::Nil;
    let mut j: usize = keep.len();

    while j > 0 {
        j -= 1;
        let x: i64 = keep[j];
        out = List::Cons(x, Box::new(out));
    }

    out
}
