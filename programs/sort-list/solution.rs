fn collect_values(l: &List, mut out: Vec<i64>) -> Vec<i64> {
    match l {
        List::Nil => out,
        List::Cons(v, next) => {
            out.push(*v);
            collect_values(&**next, out)
        }
    }
}

fn merge_sort_vec(mut v: Vec<i64>) -> Vec<i64> {
    let n = v.len();
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

            let mut tmp: Vec<i64> = Vec::new();
            let mut i = start;
            let mut j = mid;

            while i < mid && j < end {
                if v[i] <= v[j] {
                    tmp.push(v[i]);
                    i += 1;
                } else {
                    tmp.push(v[j]);
                    j += 1;
                }
            }

            while i < mid {
                tmp.push(v[i]);
                i += 1;
            }

            while j < end {
                tmp.push(v[j]);
                j += 1;
            }

            let mut k: usize = 0;
            while k < tmp.len() {
                v[start + k] = tmp[k];
                k += 1;
            }

            start = end;
        }

        width = width * 2;
    }

    v
}

pub fn sort_list(head: &List) -> List {
    let vals = collect_values(head, Vec::new());
    let vals = merge_sort_vec(vals);

    let mut out = List::Nil;
    let mut i = vals.len();

    while i > 0 {
        i -= 1;
        out = List::Cons(vals[i], Box::new(out));
    }

    out
}
