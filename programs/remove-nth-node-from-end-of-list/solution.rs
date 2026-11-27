pub fn remove_nth_from_end(head: &List, n: i64) -> List {
    let size = list_len(head);
    let target = size - n;
    remove_at(head, 0, target)
}

fn list_len(l: &List) -> i64 {
    match l {
        List::Nil => 0,
        List::Cons(_, next) => 1 + list_len(next),
    }
}

fn remove_at(l: &List, idx: i64, target: i64) -> List {
    match l {
        List::Nil => List::Nil,
        List::Cons(v, next) => {
            if idx == target {
                copy_list(next)
            } else {
                List::Cons(*v, Box::new(remove_at(next, idx + 1, target)))
            }
        }
    }
}

fn copy_list(l: &List) -> List {
    match l {
        List::Nil => List::Nil,
        List::Cons(v, next) => List::Cons(*v, Box::new(copy_list(next))),
    }
}
