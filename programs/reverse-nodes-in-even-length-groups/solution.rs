fn collect(l: &List, acc: Vec<i64>) -> Vec<i64> {
    match l {
        List::Nil => acc,
        List::Cons(v, next) => {
            let mut a: Vec<i64> = acc;
            a.push(*v);
            collect(&**next, a)
        }
    }
}

// Emits v[0], v[1], ..., v[i-1] in forward order using an accumulator.
fn build(v: Vec<i64>, i: usize, acc: List) -> List {
    if i == 0 {
        acc
    } else {
        let x = v[i - 1];
        let nxt = List::Cons(x, Box::new(acc));
        build(v, i - 1, nxt)
    }
}

pub fn reverse_even_length_groups(head: &List) -> List {
    let empty: Vec<i64> = Vec::new();
    let vals = collect(head, empty);
    let n = vals.len();

    let mut out: Vec<i64> = Vec::new();
    let mut start = 0usize;
    let mut group_len = 1usize;

    while start < n {
        let rem = n - start;
        let mut len = group_len;
        if len > rem {
            len = rem;
        }
        let rev = len % 2 == 0;
        let mut k = 0usize;
        while k < len {
            let mut idx = start + k;
            if rev {
                idx = start + len - 1 - k;
            }
            out.push(vals[idx]);
            k += 1;
        }
        start = start + len;
        group_len += 1;
    }

    let m = out.len();
    build(out, m, List::Nil)
}
