fn delete_nodes_rec(l: &List, pos: i64, keep: i64, period: i64) -> List {
    match l {
        List::Nil => List::Nil,
        List::Cons(v, next) => {
            let p = pos % period;
            let rest = delete_nodes_rec(&**next, pos + 1, keep, period);
            if p < keep {
                List::Cons(*v, Box::new(rest))
            } else {
                rest
            }
        }
    }
}

pub fn delete_nodes(head: &List, m: i64, n: i64) -> List {
    let keep = if m > 0 { m } else { 1 };
    let del = if n > 0 { n } else { 0 };
    let period = keep + del;
    delete_nodes_rec(head, 0, keep, period)
}
