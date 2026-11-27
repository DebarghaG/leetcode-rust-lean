pub fn remove_elements(head: &List, val: i64) -> List {
    match head {
        List::Nil => List::Nil,
        List::Cons(v, next) => {
            let rest = remove_elements(&**next, val);
            if *v == val {
                rest
            } else {
                List::Cons(*v, Box::new(rest))
            }
        }
    }
}
