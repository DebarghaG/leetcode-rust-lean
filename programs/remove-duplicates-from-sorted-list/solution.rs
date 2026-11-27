pub fn delete_duplicates(head: &List) -> List {
    match head {
        List::Nil => List::Nil,
        List::Cons(v, next) => {
            let rest = delete_duplicates(&**next);
            match rest {
                List::Cons(rv, tail) => {
                    if rv == *v {
                        List::Cons(rv, tail)
                    } else {
                        List::Cons(*v, Box::new(List::Cons(rv, tail)))
                    }
                }
                List::Nil => List::Cons(*v, Box::new(List::Nil)),
            }
        }
    }
}
