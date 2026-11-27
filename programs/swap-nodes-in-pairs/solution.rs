pub fn swap_pairs(head: &List) -> List {
    match head {
        List::Nil => List::Nil,
        List::Cons(v1, next1) => {
            match &**next1 {
                List::Nil => List::Cons(*v1, Box::new(List::Nil)),
                List::Cons(v2, next2) => {
                    let rest = swap_pairs(next2);
                    List::Cons(
                        *v2,
                        Box::new(List::Cons(*v1, Box::new(rest))),
                    )
                }
            }
        }
    }
}
