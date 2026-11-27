fn list_len(l: &List) -> i64 {
    match l {
        List::Nil => 0,
        List::Cons(_, next) => 1 + list_len(&**next),
    }
}

fn copy_list(l: &List) -> List {
    match l {
        List::Nil => List::Nil,
        List::Cons(v, next) => List::Cons(*v, Box::new(copy_list(&**next))),
    }
}

fn drop_first(l: &List, k: i64) -> List {
    if k == 0 {
        return copy_list(l);
    }
    match l {
        List::Nil => List::Nil,
        List::Cons(_, next) => drop_first(&**next, k - 1),
    }
}

pub fn middle_node(head: &List) -> List {
    let n = list_len(head);
    drop_first(head, n / 2)
}
