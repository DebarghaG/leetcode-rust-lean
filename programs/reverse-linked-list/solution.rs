fn reverse_acc(l: &List, acc: List) -> List {
    match l {
        List::Nil => acc,
        List::Cons(v, next) => reverse_acc(&**next, List::Cons(*v, Box::new(acc))),
    }
}

pub fn reverse_list(head: &List) -> List {
    reverse_acc(head, List::Nil)
}
