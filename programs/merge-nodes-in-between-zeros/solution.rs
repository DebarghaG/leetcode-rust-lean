fn merge_nodes_go(l: &List, started: bool, sum: i64) -> List {
    match l {
        List::Nil => List::Nil,
        List::Cons(v, next) => {
            if *v == 0 {
                if started {
                    List::Cons(sum, Box::new(merge_nodes_go(&**next, true, 0)))
                } else {
                    merge_nodes_go(&**next, true, 0)
                }
            } else {
                merge_nodes_go(&**next, started, sum + *v)
            }
        }
    }
}

pub fn merge_nodes(head: &List) -> List {
    merge_nodes_go(head, false, 0)
}
