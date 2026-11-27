fn collect_vals(l: &List, out: &mut Vec<i64>) {
    match l {
        List::Nil => {}
        List::Cons(v, next) => {
            out.push(*v);
            collect_vals(next, out);
        }
    }
}

pub fn rotate_right(head: &List, k: i64) -> List {
    let mut vals: Vec<i64> = Vec::new();
    collect_vals(head, &mut vals);

    let n = vals.len();
    if n == 0 {
        return List::Nil;
    }

    let shift = (k % (n as i64)) as usize;

    let mut out = List::Nil;
    let mut j = n;
    while j > 0 {
        j -= 1;
        let idx = (j + n - shift) % n;
        out = List::Cons(vals[idx], Box::new(out));
    }

    out
}
